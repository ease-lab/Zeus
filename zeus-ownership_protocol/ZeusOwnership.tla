--------------------------- MODULE ZeusOwnership ---------------------------

EXTENDS ZeusOwnershipMeta
\* This Module specifies the full slow-path of the Zeus ownership protocol 
\* as appears in the according paper of Eurosys'21 without faults.

\* Faults and emulated tx are added on top with the ZeusOwnershipFaults.tla spec

\* Lets implement in the following order:
\*  0. No failures  -- w/o application concurrency
\*  0.5 No failures -- w/  application concurrency
\*  1. change owner (all are reader replicas + there is or there is no owner)
\*  2. add owner 
\*  3. rm reader
\*  4. add reader
\*  5. emulate tx updates
\*  6. add fast path

-------------------------------------------------------------------------------------
\* WARNING: We need to make sure that requester REQs are executed at most once; this requires: 
\* an APP node to be sticky to its LB driver for a Key (unless failure) and send REQ msgs via a 
\* FIFO REQ channel so that driver does not re-issues REQs that have been already completed in the past!

\* We actually only need to enforce that a REQ is processed at most once by drivers 
\* (not FIFO but FIFO is the easiest way to achieve that).

\* We emulate executing only once via committedRTS (committedREQs is used to check INVARIANTS)
commit_REQ(s_ts, r_ts) == 
    /\ committedRTS'  = committedRTS  \union {r_ts}
    /\ committedREQs' = committedREQs \union {s_ts} 

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

upd_s_meta(n, ver, tb, state, driver, vec, ACKs) ==
    /\ sVector'  = [sVector     EXCEPT![n] = vec]
    /\ sRcvACKs' = [sRcvACKs    EXCEPT![n] = ACKs]
    /\ sState'   = [sState      EXCEPT![n] = state]
    /\ sDriver'  = [sDriver     EXCEPT![n] = driver]
    /\ sTS'      = [sTS         EXCEPT![n].ver = ver, ![n].tb  = tb]

upd_s_meta_driver(n, ver, tb) == upd_s_meta(n, ver, tb, "drive", n, sVector[n], {})
upd_s_meta_add_ack(n, sender) == 
    upd_s_meta(n, sTS[n].ver, sTS[n].tb, sState[n], sDriver[n], sVector[n], sRcvACKs[n] \union {sender})

upd_s_meta_apply_val(n, m) == 
    /\ IF   rTS[n].tb \notin mAliveNodes
       THEN upd_s_meta(n, sTS[n].ver, sTS[n].tb, "valid", 0, post_sVec(n, 0, sVector[n]), {}) 
       ELSE upd_s_meta(n, sTS[n].ver, sTS[n].tb, "valid", 0, post_sVec(n, rTS[n].tb, sVector[n]), {}) 
    
upd_s_meta_apply_val_n_reset_s_state(n) == 
    upd_s_meta(n, 0, 0, "valid", 0, [readers |-> {}, owner |-> 0], {}) 
    
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
        /\ upd_s_meta(n, 0, 0, "request", 0, [readers |-> {}, owner |-> 0], {})
        /\ s_send_req([ver |-> next_rTS_ver(n), tb |-> n], 0, r_type)

-------------------------------------------------------------------------------------
\* REQUESTER ACTIONS

SRequesterREQ(n) == \* Requester issues a REQ
    /\ is_valid_requester(n)
    /\ is_reader(n)
    /\ next_rTS_ver(n) <= S_MAX_VERSION \* bound execution --> Bound this in reachable states
    /\ upd_rs_meta_n_send_req(n, "change-owner") \* to limit the state space only choose change ownership
\*    /\ upd_rs_meta_n_send_req(n, choose_req(n))
    /\ unchanged_mtc

\* Requester receives NACK and replays REQ w/ higher rID
SRequesterNACK(n) ==
    /\ is_in_progress_requester(n)
    /\ rID[n] < S_MAX_VERSION \* TODO: may Bound rID to number of APP_NODES instead
    /\ \E m \in sMsgs: s_rcv_nack(m, n)
    /\ upd_r_meta(n, rTS[n].ver, n, rID[n] + 1, rType[n])
    /\ s_send_req([ver |-> rTS[n].ver, tb |-> n], rID[n] + 1, rType[n])
    /\ unchanged_mtcs
    
SRequesterRESP(n) == \* Requester receives a RESP and sends a VAL to arbiters
\E m \in sMsgs:
    /\ s_rcv_resp(m, n)  
    /\ is_in_progress_requester(n)
    /\ commit_REQ(m.sTS, rTS[n])
    /\ upd_t_meta(n, m.tVersion, "valid", tRcvACKs[n])  \* todo this is optional
    /\ upd_s_meta(n, m.sTS.ver, m.sTS.tb, "valid", 0, post_sVec(n, n, m.sVector), {})
    /\ s_send_val(m.sTS)  
    /\ unchanged_mtr 

SRequesterActions ==
  \E n \in APP_LIVE_NODES:   
     \/ SRequesterREQ (n)
     \/ SRequesterNACK(n)
     \/ SRequesterRESP(n)

-------------------------------------------------------------------------------------
\* DRIVER ACTIONS
SDriverINV(n, m) ==
        /\ s_rcv_req(m)
        /\ sState[n] = "valid"
        /\ sTS[n].ver < S_MAX_VERSION \* bound execution --> Bound this in reachable states
        /\ upd_t_meta(n, 0, tState[n], tRcvACKs[n])
        /\ upd_r_meta(n, m.rTS.ver, m.rTS.tb, m.rID, m.rType)
        /\ upd_s_meta_driver(n, sTS[n].ver + 1, n)
        /\ s_send_inv(n, n, [ver |-> sTS[n].ver + 1, tb |-> n], sVector[n], m.rTS, m.rID, m.rType)
        /\ unchanged_mc
        
SDriverNACK(n, m) ==
        /\ s_rcv_req(m)
        /\ rTS[n]    # m.rTS
        /\ sState[n] # "valid"
        /\ msg_not_exists(s_rcv_nack, m.rTS.tb) \* NACK does not exist (bound state space)
        /\ s_send_nack(m.rTS, m.rID)
        /\ unchanged_mtrcs 

SDriverACK(n, m) ==
        /\ s_rcv_ack(m, n)  
        /\ upd_s_meta_add_ack(n, m.sender)
        /\ IF m.tVersion # 0
           THEN upd_t_meta(n, m.tVersion, tState[n], tRcvACKs[n])
           ELSE unchanged_t
        /\ unchanged_Mmrc

SDriverRESP(n) ==
    /\ sState[n] = "drive"
    /\ has_rcved_all_ACKs(n)
    /\ requester_is_alive(n)
    /\ msg_not_exists(s_rcv_resp, rTS[n].tb) \* RESP does not exist (bound state space)
    /\ s_send_resp(rTS[n], sTS[n], post_sVec(n, rTS[n].tb, sVector[n]), tVersion[n]) 
    /\ unchanged_mtrcs 

SDriverActions ==
  \E n \in LB_LIVE_NODES:  
     \/ SDriverRESP(n)
     \/ \E m \in sMsgs:     
        \/ SDriverINV (n, m)
        \/ SDriverNACK(n, m)
        \/ SDriverACK (n, m)

-------------------------------------------------------------------------------------
\* LB ARBITER ACTIONS
inv_to_be_applied(n, m) ==
           \/ s_rcv_inv_greater_ts(m, n)
           \/  (s_rcv_inv_equal_ts(m, n) /\ sState[n] = "invalid" /\ m.epochID > rEID[n])

check_n_apply_inv(n, m) ==
        /\ inv_to_be_applied(n, m) 
        /\ upd_r_meta(n, m.rTS.ver, m.rTS.tb, m.rID, m.rType) 
        /\ upd_s_meta(n, m.sTS.ver, m.sTS.tb, "invalid", m.driver, m.sVector, {}) 

\* We do not model lost messages thus arbiter need not respond w/ INV when ts is smaller
SLBArbiterINV(n, m) ==
        /\ check_n_apply_inv(n, m)
        /\ \/ sState[n] # "drive" 
           \/ s_send_nack(rTS[n], rID[n])
        /\ s_send_ack(n, m.sTS, 0) 
        /\ unchanged_mtc 

SLBArbiterVAL(n, m) ==
       /\ s_rcv_val(m, n)  
       /\ upd_s_meta_apply_val(n, m)
       /\ unchanged_Mmtrc

SLBArbiterActions ==
  \E n \in LB_LIVE_NODES: \E m \in sMsgs: 
     \/ SLBArbiterINV(n, m)
     \/ SLBArbiterVAL(n, m)
     
-------------------------------------------------------------------------------------
\* (O)wner or (R)eader ARBITER ACTIONS

\* reader doesn't apply an INV but always responds with an ACK 
\* (and data if non-sharing rType and in tValid state)
SRArbiterINV(n, m) == 
        /\ is_reader(n)
        /\ tState[n] = "valid"
        /\ s_rcv_inv(m, n)
        /\ s_send_ack(n, m.sTS, tVersion[n]) 
        /\ unchanged_mtrcs 
        
SOArbiterINV(n, m) ==
        /\ is_owner(n)
        /\ m.type = "S_INV"
        /\ m.sVector.owner = n \* otherwise owner lost a VAL --> SFMOArbiterINVLostVAL 
        /\ tState[n] = "valid"
        /\ check_n_apply_inv(n, m)
        /\ s_send_ack(n, m.sTS, tVersion[n]) 
        /\ unchanged_mtc 

SOArbiterVAL(n, m) ==
       /\ s_rcv_val(m, n)  
       /\ IF sVector[n].owner = n
          THEN /\ upd_s_meta_apply_val(n, m)
          ELSE /\ upd_s_meta_apply_val_n_reset_s_state(n)
       /\ unchanged_Mmtrc

SAPPArbiterActions ==
  \E n \in APP_LIVE_NODES: \E m \in sMsgs: 
       \/ SRArbiterINV(n, m)
       \/ SOArbiterINV(n, m)
       \/ SOArbiterVAL(n, m)
       
-------------------------------------------------------------------------------------
\* Owner actions emulating tx updates
 
TOwnerINV(n) ==
    /\ upd_t_meta(n, tVersion[n] + 1, "write", {})
    /\ t_send(n, "T_INV", tVersion[n] + 1)
    /\ unchanged_mrcs 

TOwnerACK(n) ==
    \E m \in sMsgs:
    /\ t_rcv_ack(m, n)
    /\ upd_t_meta(n, tVersion[n], tState[n], tRcvACKs[n] \union {m.sender})
    /\ unchanged_Mmrcs 

TOwnerVAL(n) ==
    /\ sVector[n].readers \subseteq tRcvACKs[n] \* has received all acks from readers
    /\ upd_t_meta(n, tVersion[n], "valid", {})
    /\ t_send(n, "T_VAL", tVersion[n])
    /\ unchanged_mrcs 

\* Reader actions emulating tx updates
TReaderINV(n) ==
    \E m \in sMsgs:
    /\ t_rcv_inv(m, n)
    /\ m.tVersion > tVersion[n]
    /\ upd_t_meta(n, m.tVersion, "invalid", {})
    /\ t_send(n, "T_ACK", m.tVersion)
    /\ unchanged_mrcs 

TReaderVAL(n) ==
    \E m \in sMsgs:
    /\ t_rcv_val(m, n)
    /\ m.tVersion = tVersion[n]
    /\ upd_t_meta(n, tVersion[n], "valid", {})
    /\ unchanged_Mmrcs 
    
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
SNext == 
    \/ SInit_min_owner_rest_readers
    \/ SRequesterActions
    \/ SDriverActions 
    \/ SLBArbiterActions 
    \/ SAPPArbiterActions 
\*    \/ TOwnerReaderActions

(***************************************************************************)
(* The complete definition of the algorithm                                *)
(***************************************************************************)

Spec == SInit /\ [][SNext]_vars

Invariants == /\ ([]STypeOK) 
              /\ ([]CONSISTENT_DATA)    /\ ([]ONLY_ONE_CONC_REQ_COMMITS)
              /\ ([]AT_MOST_ONE_OWNER)  /\ ([]OWNER_LATEST_DATA) 
              /\ ([]CONSISTENT_SHARERS) /\ ([]CONSISTENT_SVECTORS) 


THEOREM Spec => Invariants
-------------------------------------------------------------------------------------
\*
\*LSpec == Spec /\ WF_vars(SNext)
\*
\*LIVENESS == \E i \in LB_NODES: []<>(sState[i] = "valid" /\ sTS[i].ver > 3)
\*-----------------------------------------------------------------------------
\*THEOREM  LSpec => LIVENESS
=============================================================================
