--------------------------- MODULE ZeusOwnership ---------------------------
EXTENDS ZeusOwnershipMeta
\* This Module specifies the full slow-path of the Zeus ownership protocol 
\* as appears in the according paper of Eurosys'21 without faults.
\* It model checks its properties in the face of concurrent conflicting 
\* requests of changing ownerships and emulated reliable commits.

\* Faults are added on top with the ZeusOwnershipFaults.tla spec

-------------------------------------------------------------------------------------
\* WARNING: We need to make sure that requester REQs are executed at most once; this requires: 
\* an APP node to be sticky to its LB driver for a Key (unless failure) and send REQ msgs via a 
\* FIFO REQ channel so that driver does not re-issues REQs that have been already completed in the past!

\* We emulate executing only once via committedRTS (committedREQs is used to check INVARIANTS)
commit_REQ(o_ts, r_ts) == 
    /\ committedRTS'  = committedRTS  \union {r_ts}
    /\ committedREQs' = committedREQs \union {o_ts} 

upd_t_meta(n, version, state, t_acks) ==
    /\ tState'   = [tState   EXCEPT![n] = state]
    /\ tVersion' = [tVersion EXCEPT![n] = version]
    /\ tRcvACKs' = [tRcvACKs EXCEPT![n] = t_acks]

upd_r_meta(n, ver, tb, id, type) ==
    /\ rID'   = [rID    EXCEPT![n] = id]
    /\ rEID'  = [rEID   EXCEPT![n] = mEID]   \* always update to latest mEID
    /\ rType' = [rType  EXCEPT![n] = type]
    /\ rTS'   = [rTS    EXCEPT![n].ver = ver, ![n].tb  = tb]

\* to update the epoch id of last message issue
upd_rEID(n) == upd_r_meta(n, rTS[n].ver, rTS[n].tb, rID[n], rType[n])

upd_o_meta(n, ver, tb, state, driver, vec, ACKs) ==
    /\ oVector'  = [oVector     EXCEPT![n] = vec]
    /\ oRcvACKs' = [oRcvACKs    EXCEPT![n] = ACKs]
    /\ oState'   = [oState      EXCEPT![n] = state]
    /\ oDriver'  = [oDriver     EXCEPT![n] = driver]
    /\ oTS'      = [oTS         EXCEPT![n].ver = ver, ![n].tb  = tb]

upd_o_meta_driver(n, ver, tb) == upd_o_meta(n, ver, tb, "drive", n, oVector[n], {})
upd_o_meta_add_ack(n, sender) == 
    upd_o_meta(n, oTS[n].ver, oTS[n].tb, oState[n], oDriver[n], oVector[n], oRcvACKs[n] \union {sender})

upd_o_meta_apply_val(n, m) == 
    /\ IF   rTS[n].tb \notin mAliveNodes
       THEN upd_o_meta(n, oTS[n].ver, oTS[n].tb, "valid", 0, post_oVec(n, 0, oVector[n]), {}) 
       ELSE upd_o_meta(n, oTS[n].ver, oTS[n].tb, "valid", 0, post_oVec(n, rTS[n].tb, oVector[n]), {}) 
    
upd_o_meta_apply_val_n_reset_o_state(n) == 
    upd_o_meta(n, 0, 0, "valid", 0, [readers |-> {}, owner |-> 0], {}) 
    
-------------------------------------------------------------------------------------
\* REQUESTER Helper operators

choose_req(n) ==
    LET choice == CHOOSE x \in {0,1} : TRUE IN 
       IF is_reader(n) 
       THEN /\ IF   choice = 0
               THEN "change-owner" 
               ELSE "remove-reader"
       ELSE /\ IF   choice = 0
               THEN "add-owner" 
               ELSE "add-reader"

max_commited_ver(S, n) == IF \A i \in S: i.tb # n THEN [ver |-> 0, tb |-> 0]
                            ELSE CHOOSE i \in S: /\ i.tb = n
                                                 /\ \A j \in S: \/ j.tb   # n
                                                                \/ j.ver <= i.ver

next_rTS_ver(n) == max_commited_ver(committedRTS, n).ver + 1

upd_rs_meta_n_send_req(n, r_type) ==
        /\ upd_r_meta(n, next_rTS_ver(n), n, 0, r_type)
        /\ upd_o_meta(n, 0, 0, "request", 0, [readers |-> {}, owner |-> 0], {})
        /\ o_send_req([ver |-> next_rTS_ver(n), tb |-> n], 0, r_type)

-------------------------------------------------------------------------------------
\* REQUESTER ACTIONS

ORequesterREQ(n) == \* Requester issues a REQ
    /\ is_valid_requester(n)
    /\ is_reader(n)
    /\ next_rTS_ver(n) <= O_MAX_VERSION \* bound execution --> Bound this in reachable states
    /\ upd_rs_meta_n_send_req(n, "change-owner") \* to limit the state space only choose change ownership
\*    /\ upd_rs_meta_n_send_req(n, choose_req(n))
    /\ unchanged_mtc

\* Requester receives NACK and replays REQ w/ higher rID
ORequesterNACK(n) ==
    /\ is_in_progress_requester(n)
    /\ rID[n] < O_MAX_VERSION \* TODO: may Bound rID to number of APP_NODES instead
    /\ \E m \in oMsgs: o_rcv_nack(m, n)
    /\ upd_r_meta(n, rTS[n].ver, n, rID[n] + 1, rType[n])
    /\ o_send_req([ver |-> rTS[n].ver, tb |-> n], rID[n] + 1, rType[n])
    /\ unchanged_mtco
    
ORequesterRESP(n) == \* Requester receives a RESP and sends a VAL to arbiters
\E m \in oMsgs:
    /\ o_rcv_resp(m, n)  
    /\ is_in_progress_requester(n)
    /\ commit_REQ(m.oTS, rTS[n])
    /\ upd_t_meta(n, m.tVersion, "valid", tRcvACKs[n])  \* todo this is optional
    /\ upd_o_meta(n, m.oTS.ver, m.oTS.tb, "valid", 0, post_oVec(n, n, m.oVector), {})
    /\ o_send_val(m.oTS)  
    /\ unchanged_mtr 

ORequesterActions ==
  \E n \in APP_LIVE_NODES:   
     \/ ORequesterREQ (n)
     \/ ORequesterNACK(n)
     \/ ORequesterRESP(n)

-------------------------------------------------------------------------------------
\* DRIVER ACTIONS
ODriverINV(n, m) ==
        /\ o_rcv_req(m)
        /\ oState[n] = "valid"
        /\ oTS[n].ver < O_MAX_VERSION \* bound execution --> Bound this in reachable states
        /\ upd_t_meta(n, 0, tState[n], tRcvACKs[n])
        /\ upd_r_meta(n, m.rTS.ver, m.rTS.tb, m.rID, m.rType)
        /\ upd_o_meta_driver(n, oTS[n].ver + 1, n)
        /\ o_send_inv(n, n, [ver |-> oTS[n].ver + 1, tb |-> n], oVector[n], m.rTS, m.rID, m.rType)
        /\ unchanged_mc
        
ODriverNACK(n, m) ==
        /\ o_rcv_req(m)
        /\ rTS[n]    # m.rTS
        /\ oState[n] # "valid"
        /\ msg_not_exists(o_rcv_nack, m.rTS.tb) \* NACK does not exist (bound state space)
        /\ o_send_nack(m.rTS, m.rID)
        /\ unchanged_mtrco 

ODriverACK(n, m) ==
        /\ o_rcv_ack(m, n)  
        /\ upd_o_meta_add_ack(n, m.sender)
        /\ IF m.tVersion # 0
           THEN upd_t_meta(n, m.tVersion, tState[n], tRcvACKs[n])
           ELSE unchanged_t
        /\ unchanged_Mmrc

ODriverRESP(n) ==
    /\ oState[n] = "drive"
    /\ has_rcved_all_ACKs(n)
    /\ requester_is_alive(n)
    /\ msg_not_exists(o_rcv_resp, rTS[n].tb) \* RESP does not exist (bound state space)
    /\ o_send_resp(rTS[n], oTS[n], post_oVec(n, rTS[n].tb, oVector[n]), tVersion[n]) 
    /\ unchanged_mtrco 

ODriverActions ==
  \E n \in LB_LIVE_NODES:  
     \/ ODriverRESP(n)
     \/ \E m \in oMsgs:     
        \/ ODriverINV (n, m)
        \/ ODriverNACK(n, m)
        \/ ODriverACK (n, m)

-------------------------------------------------------------------------------------
\* LB ARBITER ACTIONS
inv_to_be_applied(n, m) ==
           \/ o_rcv_inv_greater_ts(m, n)
           \/  (o_rcv_inv_equal_ts(m, n) /\ oState[n] = "invalid" /\ m.epochID > rEID[n])

check_n_apply_inv(n, m) ==
        /\ inv_to_be_applied(n, m) 
        /\ upd_r_meta(n, m.rTS.ver, m.rTS.tb, m.rID, m.rType) 
        /\ upd_o_meta(n, m.oTS.ver, m.oTS.tb, "invalid", m.driver, m.oVector, {}) 

\* We do not model lost messages thus arbiter need not respond w/ INV when ts is smaller
OLBArbiterINV(n, m) ==
        /\ check_n_apply_inv(n, m)
        /\ \/ oState[n] # "drive" 
           \/ o_send_nack(rTS[n], rID[n])
        /\ o_send_ack(n, m.oTS, 0) 
        /\ unchanged_mtc 

OLBArbiterVAL(n, m) ==
       /\ o_rcv_val(m, n)  
       /\ upd_o_meta_apply_val(n, m)
       /\ unchanged_Mmtrc

OLBArbiterActions ==
  \E n \in LB_LIVE_NODES: \E m \in oMsgs: 
     \/ OLBArbiterINV(n, m)
     \/ OLBArbiterVAL(n, m)
     
-------------------------------------------------------------------------------------
\* (O)wner or (R)eader ARBITER ACTIONS

\* reader doesn't apply an INV but always responds with an ACK 
\* (and data if non-sharing rType and in tValid state)
ORArbiterINV(n, m) == 
        /\ is_reader(n)
        /\ tState[n] = "valid"
        /\ o_rcv_inv(m, n)
        /\ o_send_ack(n, m.oTS, tVersion[n]) 
        /\ unchanged_mtrco 
        
OOArbiterINV(n, m) ==
        /\ is_owner(n)
        /\ m.type = "S_INV"
        /\ m.oVector.owner = n \* otherwise owner lost a VAL --> SFMOArbiterINVLostVAL 
        /\ tState[n] = "valid"
        /\ check_n_apply_inv(n, m)
        /\ o_send_ack(n, m.oTS, tVersion[n]) 
        /\ unchanged_mtc 

OOArbiterVAL(n, m) ==
       /\ o_rcv_val(m, n)  
       /\ IF oVector[n].owner = n
          THEN /\ upd_o_meta_apply_val(n, m)
          ELSE /\ upd_o_meta_apply_val_n_reset_o_state(n)
       /\ unchanged_Mmtrc

OAPPArbiterActions ==
  \E n \in APP_LIVE_NODES: \E m \in oMsgs: 
       \/ ORArbiterINV(n, m)
       \/ OOArbiterINV(n, m)
       \/ OOArbiterVAL(n, m)
       
-------------------------------------------------------------------------------------
\* Owner actions emulating tx updates
 
TOwnerINV(n) ==
    /\ upd_t_meta(n, tVersion[n] + 1, "write", {})
    /\ t_send(n, "T_INV", tVersion[n] + 1)
    /\ unchanged_mrco 

TOwnerACK(n) ==
    \E m \in oMsgs:
    /\ t_rcv_ack(m, n)
    /\ upd_t_meta(n, tVersion[n], tState[n], tRcvACKs[n] \union {m.sender})
    /\ unchanged_Mmrco 

TOwnerVAL(n) ==
    /\ oVector[n].readers \subseteq tRcvACKs[n] \* has received all acks from readers
    /\ upd_t_meta(n, tVersion[n], "valid", {})
    /\ t_send(n, "T_VAL", tVersion[n])
    /\ unchanged_mrco 

\* Reader actions emulating tx updates
TReaderINV(n) ==
    \E m \in oMsgs:
    /\ t_rcv_inv(m, n)
    /\ m.tVersion > tVersion[n]
    /\ upd_t_meta(n, m.tVersion, "invalid", {})
    /\ t_send(n, "T_ACK", m.tVersion)
    /\ unchanged_mrco 

TReaderVAL(n) ==
    \E m \in oMsgs:
    /\ t_rcv_val(m, n)
    /\ m.tVersion = tVersion[n]
    /\ upd_t_meta(n, tVersion[n], "valid", {})
    /\ unchanged_Mmrco 
    
TOwnerReaderActions ==
  \E n \in APP_LIVE_NODES:
    \/ /\ is_valid_owner(n)
       /\ \/ TOwnerINV(n)
          \/ TOwnerACK(n)
          \/ TOwnerVAL(n)
    \/ /\ is_reader(n)
       /\ \/ TReaderINV(n)
          \/ TReaderVAL(n)

-------------------------------------------------------------------------------------
\* Modeling Sharding protocol (Requester and Arbiter actions)
ONext == 
    \/ OInit_min_owner_rest_readers
    \/ ORequesterActions
    \/ ODriverActions 
    \/ OLBArbiterActions 
    \/ OAPPArbiterActions 
\*    \/ TOwnerReaderActions

(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == OInit /\ [][ONext]_vars

Invariants == /\ ([]OTypeOK) 
              /\ ([]CONSISTENT_DATA)    /\ ([]ONLY_ONE_CONC_REQ_COMMITS)
              /\ ([]AT_MOST_ONE_OWNER)  /\ ([]OWNER_LATEST_DATA) 
              /\ ([]CONSISTENT_SHARERS) /\ ([]CONSISTENT_OVECTORS) 


THEOREM Spec => Invariants
-------------------------------------------------------------------------------------
\*
\*LSpec == Spec /\ WF_vars(ONext)
\*
\*LIVENESS == \E i \in LB_NODES: []<>(oState[i] = "valid" /\ oTS[i].ver > 3)
\*-----------------------------------------------------------------------------
\*THEOREM  LSpec => LIVENESS
=============================================================================
