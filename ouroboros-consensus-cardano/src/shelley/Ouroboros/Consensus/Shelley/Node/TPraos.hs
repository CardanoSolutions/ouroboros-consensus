{-# LANGUAGE DataKinds               #-}
{-# LANGUAGE DuplicateRecordFields   #-}
{-# LANGUAGE FlexibleContexts        #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE GADTs                   #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE NamedFieldPuns          #-}
{-# LANGUAGE OverloadedStrings       #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RecordWildCards         #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeApplications        #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Ouroboros.Consensus.Shelley.Node.TPraos (
    MaxMajorProtVer (..)
  , ProtocolParamsAllegra (..)
  , ProtocolParamsAlonzo (..)
  , ProtocolParamsMary (..)
  , ProtocolParamsShelley (..)
  , ProtocolParamsShelleyBased (..)
  , SL.Nonce (..)
  , SL.ProtVer (..)
  , SL.ShelleyGenesis (..)
  , SL.ShelleyGenesisStaking (..)
  , SL.emptyGenesisStaking
  , ShelleyLeaderCredentials (..)
  , protocolInfoShelley
  , protocolInfoTPraosShelleyBased
  , registerGenesisStaking
  , registerInitialFunds
  , shelleyBlockForging
  , shelleySharedBlockForging
  , validateGenesis
  ) where

import qualified Cardano.Crypto.VRF as VRF
import qualified Cardano.Ledger.Coin as SL
import qualified Cardano.Ledger.Core as Core
import qualified Cardano.Ledger.Shelley.API as SL
import qualified Cardano.Ledger.Shelley.LedgerState as SL
                     (incrementalStakeDistr, updateStakeDistribution)
import qualified Cardano.Ledger.Shelley.Translation as SL
                     (emptyFromByronTranslationContext)
import qualified Cardano.Ledger.UMap as UM
import           Cardano.Ledger.Val (coin, inject, (<->))
import qualified Cardano.Protocol.TPraos.API as SL
import qualified Cardano.Protocol.TPraos.OCert as Absolute (KESPeriod (..))
import qualified Cardano.Protocol.TPraos.OCert as SL
import           Cardano.Slotting.EpochInfo
import           Cardano.Slotting.Time (mkSlotLength)
import           Control.Monad.Except (Except)
import           Data.Bifunctor (first)
import qualified Data.ListMap as ListMap
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.SOP.Strict
import qualified Data.Text as Text
import           GHC.Stack (HasCallStack)
import           Ouroboros.Consensus.Block
import           Ouroboros.Consensus.Config
import qualified Ouroboros.Consensus.HardFork.History as History
import           Ouroboros.Consensus.HeaderValidation
import           Ouroboros.Consensus.Ledger.Abstract
import           Ouroboros.Consensus.Ledger.Extended
import           Ouroboros.Consensus.Mempool (TxLimits)
import qualified Ouroboros.Consensus.Mempool as Mempool
import           Ouroboros.Consensus.Node.ProtocolInfo
import           Ouroboros.Consensus.Protocol.Abstract
import           Ouroboros.Consensus.Protocol.Ledger.HotKey (HotKey)
import qualified Ouroboros.Consensus.Protocol.Ledger.HotKey as HotKey
import           Ouroboros.Consensus.Protocol.Praos.Common
import           Ouroboros.Consensus.Protocol.TPraos
import           Ouroboros.Consensus.Shelley.Eras
import           Ouroboros.Consensus.Shelley.Ledger
import           Ouroboros.Consensus.Shelley.Ledger.Inspect ()
import           Ouroboros.Consensus.Shelley.Ledger.NetworkProtocolVersion ()
import           Ouroboros.Consensus.Shelley.Node.Common
                     (ProtocolParamsShelleyBased (..), ShelleyEraWithCrypto,
                     ShelleyLeaderCredentials (..), shelleyBlockIssuerVKey)
import           Ouroboros.Consensus.Shelley.Node.Serialisation ()
import           Ouroboros.Consensus.Shelley.Protocol.TPraos ()
import           Ouroboros.Consensus.Util.Assert
import           Ouroboros.Consensus.Util.IOLike

{-------------------------------------------------------------------------------
  BlockForging
-------------------------------------------------------------------------------}

-- | Create a 'BlockForging' record for a single era.
--
-- In case the same credentials should be shared across multiple Shelley-based
-- eras, use 'shelleySharedBlockForging'.
shelleyBlockForging ::
     forall m era c.
      ( ShelleyCompatible (TPraos c) era
      , PraosCrypto c
      , c ~ EraCrypto era
      , TxLimits (ShelleyBlock (TPraos c) era)
      , IOLike m
      )
  => TPraosParams
  -> Mempool.TxOverrides (ShelleyBlock (TPraos c) era)
  -> ShelleyLeaderCredentials (EraCrypto era)
  -> m (BlockForging m (ShelleyBlock (TPraos c) era))
shelleyBlockForging tpraosParams maxTxCapacityOverrides credentials = do
    hotKey <- HotKey.mkHotKey @m @c initSignKey startPeriod tpraosMaxKESEvo
    pure $ shelleySharedBlockForging hotKey slotToPeriod credentials maxTxCapacityOverrides
  where
    TPraosParams {tpraosMaxKESEvo, tpraosSlotsPerKESPeriod} = tpraosParams

    ShelleyLeaderCredentials {
        shelleyLeaderCredentialsInitSignKey = initSignKey
      , shelleyLeaderCredentialsCanBeLeader = canBeLeader
      } = credentials

    startPeriod :: Absolute.KESPeriod
    startPeriod = SL.ocertKESPeriod $ praosCanBeLeaderOpCert canBeLeader

    slotToPeriod :: SlotNo -> Absolute.KESPeriod
    slotToPeriod (SlotNo slot) =
      SL.KESPeriod $ fromIntegral $ slot `div` tpraosSlotsPerKESPeriod

-- | Create a 'BlockForging' record safely using a given 'Hotkey'.
--
-- The name of the era (separated by a @_@) will be appended to each
-- 'forgeLabel'.
shelleySharedBlockForging ::
     forall m c era.
     ( PraosCrypto c
     , ShelleyEraWithCrypto c (TPraos c) era
     , IOLike m
     )
  => HotKey c m
  -> (SlotNo -> Absolute.KESPeriod)
  -> ShelleyLeaderCredentials c
  -> Mempool.TxOverrides (ShelleyBlock (TPraos c) era)
  -> BlockForging m     (ShelleyBlock (TPraos c) era)
shelleySharedBlockForging hotKey slotToPeriod credentials maxTxCapacityOverrides =
    BlockForging {
        forgeLabel       = label <> "_" <> shelleyBasedEraName (Proxy @era)
      , canBeLeader      = canBeLeader
      , updateForgeState = \_ curSlot _ ->
                               forgeStateUpdateInfoFromUpdateInfo <$>
                                 HotKey.evolve hotKey (slotToPeriod curSlot)
      , checkCanForge    = \cfg curSlot _tickedChainDepState ->
                               tpraosCheckCanForge
                                 (configConsensus cfg)
                                 forgingVRFHash
                                 curSlot
      , forgeBlock       = \cfg ->
          forgeShelleyBlock
            hotKey
            canBeLeader
            cfg
            maxTxCapacityOverrides
      }
  where
    ShelleyLeaderCredentials {
        shelleyLeaderCredentialsCanBeLeader = canBeLeader
      , shelleyLeaderCredentialsLabel       = label
      } = credentials

    forgingVRFHash :: SL.Hash c (SL.VerKeyVRF c)
    forgingVRFHash =
          SL.hashVerKeyVRF
        . VRF.deriveVerKeyVRF
        . praosCanBeLeaderSignKeyVRF
        $ canBeLeader

{-------------------------------------------------------------------------------
  ProtocolInfo
-------------------------------------------------------------------------------}

-- | Check the validity of the genesis config. To be used in conjunction with
-- 'assertWithMsg'.
validateGenesis ::
     PraosCrypto c
  => SL.ShelleyGenesis c -> Either String ()
validateGenesis = first errsToString . SL.validateGenesis
  where
    errsToString :: [SL.ValidationErr] -> String
    errsToString errs =
        Text.unpack $ Text.unlines
          ("Invalid genesis config:" : map SL.describeValidationErr errs)

-- | Parameters needed to run Shelley
data ProtocolParamsShelley c = ProtocolParamsShelley {
      shelleyProtVer                :: SL.ProtVer
    , shelleyMaxTxCapacityOverrides :: Mempool.TxOverrides (ShelleyBlock(TPraos c) (ShelleyEra c) )
    }

-- | Parameters needed to run Allegra
data ProtocolParamsAllegra c = ProtocolParamsAllegra {
      allegraProtVer                :: SL.ProtVer
    , allegraMaxTxCapacityOverrides :: Mempool.TxOverrides (ShelleyBlock (TPraos c) (AllegraEra c) )
    }

-- | Parameters needed to run Mary
data ProtocolParamsMary c = ProtocolParamsMary {
      maryProtVer                :: SL.ProtVer
    , maryMaxTxCapacityOverrides :: Mempool.TxOverrides (ShelleyBlock (TPraos c) (MaryEra c) )
    }

-- | Parameters needed to run Alonzo
data ProtocolParamsAlonzo c = ProtocolParamsAlonzo {
      alonzoProtVer                :: SL.ProtVer
    , alonzoMaxTxCapacityOverrides :: Mempool.TxOverrides (ShelleyBlock (TPraos c) (AlonzoEra c) )
    }

protocolInfoShelley ::
     forall m c.
      ( IOLike m
      , PraosCrypto c
      , ShelleyCompatible (TPraos c) (ShelleyEra c)
      , TxLimits (ShelleyBlock (TPraos c) (ShelleyEra c))
      )
  => ProtocolParamsShelleyBased (ShelleyEra c)
  -> ProtocolParamsShelley c
  -> ProtocolInfo m (ShelleyBlock (TPraos c)(ShelleyEra c) )
protocolInfoShelley protocolParamsShelleyBased
                    ProtocolParamsShelley {
                        shelleyProtVer                = protVer
                      , shelleyMaxTxCapacityOverrides = maxTxCapacityOverrides
                      } =
    protocolInfoTPraosShelleyBased
      protocolParamsShelleyBased
      ((), SL.emptyFromByronTranslationContext)
      protVer
      maxTxCapacityOverrides

protocolInfoTPraosShelleyBased ::
     forall m era c.
      ( IOLike m
      , PraosCrypto c
      , ShelleyCompatible (TPraos c) era
      , TxLimits (ShelleyBlock (TPraos c) era)
      , c ~ EraCrypto era
      )
  => ProtocolParamsShelleyBased era
  -> (SL.AdditionalGenesisConfig era, Core.TranslationContext era)
  -> SL.ProtVer
  -> Mempool.TxOverrides (ShelleyBlock (TPraos c) era)
  -> ProtocolInfo m     (ShelleyBlock (TPraos c) era)
protocolInfoTPraosShelleyBased ProtocolParamsShelleyBased {
                             shelleyBasedGenesis           = genesis
                           , shelleyBasedInitialNonce      = initialNonce
                           , shelleyBasedLeaderCredentials = credentialss
                           }
                         (additionalGenesisConfig, translationContext)
                         protVer
                         maxTxCapacityOverrides =
    assertWithMsg (validateGenesis genesis) $
    ProtocolInfo {
        pInfoConfig       = topLevelConfig
      , pInfoInitLedger   = initExtLedgerState
      , pInfoBlockForging =
          traverse
            (shelleyBlockForging tpraosParams maxTxCapacityOverrides)
            credentialss
      }
  where
    maxMajorProtVer :: MaxMajorProtVer
    maxMajorProtVer = MaxMajorProtVer $ SL.pvMajor protVer

    topLevelConfig :: TopLevelConfig (ShelleyBlock (TPraos c) era)
    topLevelConfig = TopLevelConfig {
        topLevelConfigProtocol = consensusConfig
      , topLevelConfigLedger   = ledgerConfig
      , topLevelConfigBlock    = blockConfig
      , topLevelConfigCodec    = ShelleyCodecConfig
      , topLevelConfigStorage  = storageConfig
      }

    consensusConfig :: ConsensusConfig (BlockProtocol (ShelleyBlock (TPraos c) era))
    consensusConfig = TPraosConfig {
        tpraosParams
      , tpraosEpochInfo = epochInfo
      }

    ledgerConfig :: LedgerConfig (ShelleyBlock (TPraos c) era)
    ledgerConfig = mkShelleyLedgerConfig genesis translationContext epochInfo maxMajorProtVer

    epochInfo :: EpochInfo (Except History.PastHorizonException)
    epochInfo =
        fixedEpochInfo
          (SL.sgEpochLength genesis)
          (mkSlotLength $ SL.fromNominalDiffTimeMicro $ SL.sgSlotLength genesis)

    tpraosParams :: TPraosParams
    tpraosParams = mkTPraosParams maxMajorProtVer initialNonce genesis

    blockConfig :: BlockConfig (ShelleyBlock (TPraos c) era)
    blockConfig =
        mkShelleyBlockConfig
          protVer
          genesis
          (shelleyBlockIssuerVKey <$> credentialss)

    storageConfig :: StorageConfig (ShelleyBlock (TPraos c) era)
    storageConfig = ShelleyStorageConfig {
          shelleyStorageConfigSlotsPerKESPeriod = tpraosSlotsPerKESPeriod tpraosParams
        , shelleyStorageConfigSecurityParam     = tpraosSecurityParam     tpraosParams
        }

    initLedgerState :: LedgerState (ShelleyBlock (TPraos c) era)
    initLedgerState = ShelleyLedgerState {
        shelleyLedgerTip        = Origin
      , shelleyLedgerState      =
          registerGenesisStaking (SL.sgStaking genesis) $
            SL.initialState genesis additionalGenesisConfig
      , shelleyLedgerTransition = ShelleyTransitionInfo {shelleyAfterVoting = 0}
      }

    initChainDepState :: TPraosState c
    initChainDepState = TPraosState Origin $
      SL.initialChainDepState initialNonce (SL.sgGenDelegs genesis)

    initExtLedgerState :: ExtLedgerState (ShelleyBlock (TPraos c) era)
    initExtLedgerState = ExtLedgerState {
        ledgerState = initLedgerState
      , headerState = genesisHeaderState initChainDepState
      }

{-------------------------------------------------------------------------------
  Register genesis staking
-------------------------------------------------------------------------------}

-- | Register the initial staking information in the 'SL.NewEpochState'.
--
-- HERE BE DRAGONS! This function is intended to help in testing.
--
-- In production, the genesis should /not/ contain any initial staking.
--
-- Any existing staking information is overridden, but the UTxO is left
-- untouched.
--
-- TODO adapt and reuse @registerGenesisStaking@ from @cardano-ledger@.
registerGenesisStaking ::
     forall era. ShelleyBasedEra era
  => SL.ShelleyGenesisStaking (EraCrypto era)
  -> SL.NewEpochState era
  -> SL.NewEpochState era
registerGenesisStaking staking nes = nes {
      SL.nesEs = epochState {
          SL.esLState = ledgerState {
          SL.lsCertState = dpState {
              SL.certDState = dState'
            , SL.certPState = pState'
            }
        }
        , SL.esSnapshots = (SL.esSnapshots epochState) {
              SL.ssStakeMark = initSnapShot,
              SL.ssStakeMarkPoolDistr = SL.calculatePoolDistr initSnapShot
            }
        }

    -- Note that this is only applicable in the initial configuration where
    -- there is no existing stake distribution, since it would completely
    -- overwrite any such thing.
    , SL.nesPd = SL.calculatePoolDistr initSnapShot
    }
  where
    SL.ShelleyGenesisStaking { sgsPools, sgsStake } = staking
    SL.NewEpochState { nesEs = epochState } = nes
    ledgerState = SL.esLState epochState
    dpState = SL.lsCertState ledgerState

    -- New delegation state. Since we're using base addresses, we only care
    -- about updating the '_delegations' field.
    --
    -- See STS DELEG for details
    dState' :: SL.DState era
    dState' = (SL.certDState dpState) {
          SL.dsUnified = UM.unify
            ( Map.map (const $ UM.RDPair (SL.CompactCoin 0) (SL.CompactCoin 0))
                      . Map.mapKeys SL.KeyHashObj
                      $ sgsStakeMap)
            ( Map.mapKeys SL.KeyHashObj sgsStakeMap )
            mempty
        }
        where sgsStakeMap = ListMap.toMap sgsStake

    -- We consider pools as having been registered in slot 0
    -- See STS POOL for details
    pState' :: SL.PState era
    pState' = (SL.certPState dpState) {
          SL.psStakePoolParams = ListMap.toMap sgsPools
        }

    pp = SL.esPp epochState

    -- The new stake distribution is made on the basis of a snapshot taken
    -- during the previous epoch. We create a "fake" snapshot in order to
    -- establish an initial stake distribution.
    initSnapShot :: SL.SnapShot (EraCrypto era)
    initSnapShot =
      -- Since we build a stake from nothing, we first initialise an
      -- 'IncrementalStake' as empty, and then:
      --
      -- 1. Add the initial UTxO, whilst deleting nothing.
      -- 2. Update the stake map given the initial delegation.
      SL.incrementalStakeDistr
        pp
        -- Note that 'updateStakeDistribution' takes first the set of UTxO to
        -- delete, and then the set to add. In our case, there is nothing to
        -- delete, since this is an initial UTxO set.
        (SL.updateStakeDistribution pp mempty mempty (SL.utxosUtxo (SL.lsUTxOState ledgerState)))
        dState'
        pState'

-- | Register the initial funds in the 'SL.NewEpochState'.
--
-- HERE BE DRAGONS! This function is intended to help in testing.
--
-- In production, the genesis should /not/ contain any initial funds.
--
-- The given funds are /added/ to the existing UTxO.
--
-- PRECONDITION: the given funds must not be part of the existing UTxO.
-- > forall (addr, _) in initialFunds.
-- >    Map.notElem (SL.initialFundsPseudoTxIn addr) existingUTxO
--
-- PROPERTY:
-- >    genesisUTxO genesis
-- > == <genesisUTxO'> (sgInitialFunds genesis)
-- > == <extractUTxO> (registerInitialFunds (sgInitialFunds genesis)
-- >                                        <empty NewEpochState>)
--
-- TODO move to @cardano-ledger-specs@.
registerInitialFunds ::
     forall era.
     ( ShelleyBasedEra era
     , HasCallStack
     )
  => Map (SL.Addr (EraCrypto era)) SL.Coin
  -> SL.NewEpochState era
  -> SL.NewEpochState era
registerInitialFunds initialFunds nes = nes {
      SL.nesEs = epochState {
          SL.esAccountState = accountState'
        , SL.esLState       = ledgerState'
        }
    }
  where
    epochState   = SL.nesEs          nes
    accountState = SL.esAccountState epochState
    ledgerState  = SL.esLState       epochState
    utxoState    = SL.lsUTxOState    ledgerState
    utxo         = SL.utxosUtxo      utxoState
    reserves     = SL.asReserves     accountState

    initialFundsUtxo :: SL.UTxO era
    initialFundsUtxo = SL.UTxO $ Map.fromList [
          (txIn, txOut)
        | (addr, amount) <- Map.toList initialFunds
        ,  let txIn  = SL.initialFundsPseudoTxIn addr
               txOut = Core.mkBasicTxOut addr (inject amount)
        ]

    utxo' = mergeUtxoNoOverlap utxo initialFundsUtxo

    -- Update the reserves
    accountState' = accountState {
          SL.asReserves = reserves <-> coin (SL.balance initialFundsUtxo)
        }

    -- Since we only add entries to our UTxO, rather than spending them, there
    -- is nothing to delete in the incremental update.
    utxoToDel     = SL.UTxO mempty
    ledgerState'  = ledgerState {
          SL.lsUTxOState = utxoState {
              SL.utxosUtxo        = utxo',
              -- Normally we would incrementally update here. But since we pass
              -- the full UTxO as "toAdd" rather than a delta, we simply
              -- reinitialise the full incremental stake.
              SL.utxosStakeDistr =
                  SL.updateStakeDistribution (SL.esPp epochState) mempty utxoToDel utxo'
            }
        }

    -- | Merge two UTxOs, throw an 'error' in case of overlap
    mergeUtxoNoOverlap ::
         HasCallStack
      => SL.UTxO era -> SL.UTxO era -> SL.UTxO era
    mergeUtxoNoOverlap (SL.UTxO m1) (SL.UTxO m2) = SL.UTxO $
        Map.unionWithKey
          (\k _ _ -> error $ "initial fund part of UTxO: " <> show k)
          m1
          m2
