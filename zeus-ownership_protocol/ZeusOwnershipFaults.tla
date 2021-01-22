--------------------------- MODULE ZeusOwnershipFaults ---------------------------

EXTENDS rVNF_sharding

sharing_ok == \A nn \in APP_LIVE_NODES: \/ ~has_data(nn)
                                        \/ tState[nn] = "valid"
    
arb_replay(n) == 
    /\ upd_rEID(n)
    /\ upd_s_meta_driver(n, sTS[n].ver, sTS[n].tb)
    /\ s_send_inv(n, n, sTS[n], sVector[n], rTS[n], rID[n], rType[n])
    
    
-------------------------------------------------------------------------------------
\* Requester replays msg after a failure
SFRequester == 
  \E n \in APP_LIVE_NODES: 
     /\ sState[n] = "request"
     /\ rEID[n] < mEID 
     /\ upd_rEID(n)
     /\ s_send_req(rTS[n], rID[n], rType[n])
     /\ unchanged_mtcs

SFDriverRequester ==    \* waits for sharing-ok + computes next sVec transitions to valid +
                        \* send vals with the proper changes in the sVec
  \E n \in LB_LIVE_NODES: 
    /\ sState[n] = "drive"
    /\ has_rcved_all_ACKs(n)
    /\ ~requester_is_alive(n)
    /\ s_send_val(sTS[n]) 
    /\ upd_s_meta(n, sTS[n].ver, sTS[n].tb, "valid", 0, post_sVec(n, 0, sVector[n]), {}) 
    /\ unchanged_mtrc 

SFArbReplay == \* drivers resets acks and replays msg on arbiter failures
               \* if the failed arbiter was an owner we need to wait for sharing-ok 
               \* for convinience arb-replays happen on any failure (e.g., requester)
  \E n \in mAliveNodes: 
        /\ (sState[n] = "drive" \/ sState[n] = "invalid")
        /\ (n \in LB_LIVE_NODES \/ sVector[n].owner = n)
        /\ rEID[n] < mEID 
        /\ \/ sVector[n].owner \in mAliveNodes
           \/ sharing_ok
        /\ arb_replay(n)
        /\ unchanged_mtc
        
SLBArbiterACK == \* ACK an INV message which has the same as local s_ts but wasn't applied 
  \E n \in LB_LIVE_NODES: \E m \in sMsgs:
    /\ ~inv_to_be_applied(n, m)
    /\ s_rcv_inv_equal_ts(m, n)
    /\ s_send_ack(n, m.sTS, 0) 
    /\ unchanged_mtrcs 

-------------------------------------------------------------------------------------
\* INV response to an owner who did an arb-replay due to a lost val
SFMOArbiterLostVALOldReplay ==
    \E l \in LB_LIVE_NODES: \E a \in APP_LIVE_NODES:
    /\ sState[a] = "drive"
    /\ sVector[a].owner = a
    /\ is_greaterTS(sTS[l], sTS[a])
    /\ s_send_inv(l, l, sTS[l], sVector[l], rTS[l], rID[l], rType[l])
    /\ unchanged_mtrcs 

\* message failures
SFMOArbiterINVLostVAL ==  \* An INV is received (w/ higher ts) to a non-valid owner 
                          \* who lost a VAL for the message that demoted him
\E n \in APP_LIVE_NODES: \E m \in sMsgs:
    /\ sVector[n].owner = n
    /\ s_rcv_inv_greater_ts(m, n)
    /\ m.sVector.owner # n
    /\ upd_s_meta_apply_val_n_reset_s_state(n)
    /\ s_send_ack(n, m.sTS, tVersion[n]) 
    /\ unchanged_mtrc
                          
SFMRequesterVALReplay ==    \* Requester receives a RESP (already applied) 
                            \* and re-sends a VAL to arbiters
\E n \in APP_LIVE_NODES: \E m \in sMsgs:
    /\ s_rcv_resp(m, n)  
    /\ m.rTS.tb = n
    /\ m.sTS    = sTS[n]
\*    /\ s_send_val(m.sTS, m.sVector)  
    /\ s_send_val(m.sTS)
    /\ unchanged_mtrcs 

-------------------------------------------------------------------------------------
block_owner_failures_if_not_in_tx_valid_state(n) ==
    \/ has_valid_data(n)
    \/ ~is_valid_owner(n)

\* Emulate a node failure if there more than 2 alive nodes in LIVE_NODE_SET
nodeFailure(n, LIVE_NODE_SET) == 
    /\ n \in LIVE_NODE_SET 
\*    /\ block_owner_failures_if_not_in_valid_state(n)
    /\ Cardinality(LIVE_NODE_SET) > 2
    \* Update Membership and epoch id
    /\ mEID'        = mEID + 1
    /\ mAliveNodes' = mAliveNodes \ {n} 
    \* Remove failed node from sVectors 
    /\ sVector' = [l \in S_NODES |-> [readers |-> sVector[l].readers \ {n},
                                      owner   |-> IF   sVector[l].owner = n 
                                                  THEN 0
                                                  ELSE sVector[l].owner   ]]
    /\ unchanged_Mtrc
    /\ UNCHANGED <<sState, sDriver, sRcvACKs, sTS>>

-------------------------------------------------------------------------------------
FNext == 
    \/ SFRequester
    \/ SFDriverRequester
    \/ SFArbReplay
    \/ SLBArbiterACK
    \/ SFMOArbiterINVLostVAL
    \/ SFMRequesterVALReplay 
    \/ SFMOArbiterLostVALOldReplay
    
SFNext == 
    \/ SNext 
    \/ FNext
    \/ \E n \in mAliveNodes: 
        \/ nodeFailure(n, LB_LIVE_NODES)  \* emulate LB node failures
        \/ nodeFailure(n, APP_LIVE_NODES) \* emulate application node failures

(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

SFSpec == SInit /\ [][SFNext]_vars

THEOREM SFSpec => Invariants
=============================================================================
