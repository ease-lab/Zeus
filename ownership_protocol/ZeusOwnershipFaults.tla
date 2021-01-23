--------------------------- MODULE ZeusOwnershipFaults ---------------------------

EXTENDS ZeusOwnership

sharing_ok == \A nn \in APP_LIVE_NODES: \/ ~has_data(nn)
                                        \/ tState[nn] = "valid"
    
arb_replay(n) == 
    /\ upd_rEID(n)
    /\ upd_o_meta_driver(n, oTS[n].ver, oTS[n].tb)
    /\ o_send_inv(n, n, oTS[n], oVector[n], rTS[n], rID[n], rType[n])
    
    
-------------------------------------------------------------------------------------
\* Requester replays msg after a failure
OFRequester == 
  \E n \in APP_LIVE_NODES: 
     /\ oState[n] = "request"
     /\ rEID[n] < mEID 
     /\ upd_rEID(n)
     /\ o_send_req(rTS[n], rID[n], rType[n])
     /\ unchanged_mtco

OFDriverRequester ==    \* waits for sharing-ok + computes next oVec transitions to valid +
                        \* send vals with the proper changes in the oVec
  \E n \in LB_LIVE_NODES: 
    /\ oState[n] = "drive"
    /\ has_rcved_all_ACKs(n)
    /\ ~requester_is_alive(n)
    /\ o_send_val(oTS[n]) 
    /\ upd_o_meta(n, oTS[n].ver, oTS[n].tb, "valid", 0, post_oVec(n, 0, oVector[n]), {}) 
    /\ unchanged_mtrc 

OFArbReplay == \* drivers resets acks and replays msg on arbiter failures
               \* if the failed arbiter was an owner we need to wait for sharing-ok 
               \* for convinience arb-replays happen on any failure (e.g., requester)
  \E n \in mAliveNodes: 
        /\ (oState[n] = "drive" \/ oState[n] = "invalid")
        /\ (n \in LB_LIVE_NODES \/ oVector[n].owner = n)
        /\ rEID[n] < mEID 
        /\ \/ oVector[n].owner \in mAliveNodes
           \/ sharing_ok
        /\ arb_replay(n)
        /\ unchanged_mtc
        
OLBArbiterACK == \* ACK an INV message which has the same as local s_ts but wasn't applied 
  \E n \in LB_LIVE_NODES: \E m \in oMsgs:
    /\ ~inv_to_be_applied(n, m)
    /\ o_rcv_inv_equal_ts(m, n)
    /\ o_send_ack(n, m.oTS, 0) 
    /\ unchanged_mtrco 

-------------------------------------------------------------------------------------
\* INV response to an owner who did an arb-replay due to a lost val
OFMOArbiterLostVALOldReplay ==
    \E l \in LB_LIVE_NODES: \E a \in APP_LIVE_NODES:
    /\ oState[a] = "drive"
    /\ oVector[a].owner = a
    /\ is_greaterTS(oTS[l], oTS[a])
    /\ o_send_inv(l, l, oTS[l], oVector[l], rTS[l], rID[l], rType[l])
    /\ unchanged_mtrco 

\* message failures
OFMOArbiterINVLostVAL ==  \* An INV is received (w/ higher ts) to a non-valid owner 
                          \* who lost a VAL for the message that demoted him
\E n \in APP_LIVE_NODES: \E m \in oMsgs:
    /\ oVector[n].owner = n
    /\ o_rcv_inv_greater_ts(m, n)
    /\ m.oVector.owner # n
    /\ upd_o_meta_apply_val_n_reset_o_state(n)
    /\ o_send_ack(n, m.oTS, tVersion[n]) 
    /\ unchanged_mtrc
                          
OFMRequesterVALReplay ==    \* Requester receives a RESP (already applied) 
                            \* and re-sends a VAL to arbiters
\E n \in APP_LIVE_NODES: \E m \in oMsgs:
    /\ o_rcv_resp(m, n)  
    /\ m.rTS.tb = n
    /\ m.oTS    = oTS[n]
    /\ o_send_val(m.oTS)
    /\ unchanged_mtrco 

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
    \* Remove failed node from oVectors 
    /\ oVector' = [l \in O_NODES |-> [readers |-> oVector[l].readers \ {n},
                                      owner   |-> IF   oVector[l].owner = n 
                                                  THEN 0
                                                  ELSE oVector[l].owner   ]]
    /\ unchanged_Mtrc
    /\ UNCHANGED <<oState, oDriver, oRcvACKs, oTS>>

-------------------------------------------------------------------------------------
FNext == 
    \/ OFRequester
    \/ OFDriverRequester
    \/ OFArbReplay
    \/ OLBArbiterACK
    \/ OFMOArbiterINVLostVAL
    \/ OFMRequesterVALReplay 
    \/ OFMOArbiterLostVALOldReplay
    
OFNext == 
    \/ ONext 
    \/ FNext
    \/ \E n \in mAliveNodes: 
        \/ nodeFailure(n, LB_LIVE_NODES)  \* emulate LB node failures
        \/ nodeFailure(n, APP_LIVE_NODES) \* emulate application node failures

(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

SFSpec == OInit /\ [][OFNext]_vars

THEOREM SFSpec => Invariants
=============================================================================
