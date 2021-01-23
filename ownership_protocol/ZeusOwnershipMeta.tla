--------------------------- MODULE ZeusOwnershipMeta ---------------------------

EXTENDS     Integers, FiniteSets

CONSTANTS   \* LB_NODES and APP_NODES must not intersect and neither should contain 0.
            LB_NODES, 
            APP_NODES,
            O_MAX_VERSION,
            O_MAX_FAILURES,
            O_MAX_DATA_VERSION
                      

VARIABLES   \* variable prefixes --> o: ownership, r: request, t: transactional, m: membership 
            \* VECTORS indexed by node_id
            oTS,
            oState,
            oDriver,
            oVector,    \* No readers/owner: .readers = {} / .owner = 0 
            oRcvACKs,
            \* 
            rTS,
            rID,
            rType,
            rEID,        \* since we do not have message loss timeouts we use this to 
                         \* track epoch of last issued INVs for replays
            tState,
            tVersion,     \* tVesion sufice to represent tData | = 0 --> no data | > 0 data (reader / owner)
            tRcvACKs,
            \* GLOBAL variables 
            oMsgs,
            mAliveNodes,  \* membership
            mEID,         \* membership epoch id
            committedREQs, \* only to check invariant that exactly one of concurrent REQs is committed
            committedRTS  \* only to emulate FIFO REQ channels (i.e., do not re execute same client requests)

vars == << oTS, oState, oDriver, oVector, oRcvACKs, rTS, rID, rType, rEID,        
           tState, tVersion, tRcvACKs, oMsgs, mAliveNodes, mEID, committedREQs, committedRTS>>

\* Helper operators 
O_NODES        == LB_NODES  \union APP_NODES
O_NODES_0      == O_NODES   \union {0}
LB_NODES_0     == LB_NODES  \union {0}
APP_NODES_0    == APP_NODES \union {0} 
LB_LIVE_NODES  == LB_NODES  \intersect mAliveNodes
APP_LIVE_NODES == APP_NODES \intersect mAliveNodes
LB_LIVE_ARBITERS(driver) == LB_LIVE_NODES \ {driver} \* all arbiters except driver and owner

ASSUME LB_NODES \intersect APP_NODES = {}
ASSUME \A k \in O_NODES: k # 0 \* we use 0 as the default noop

-------------------------------------------------------------------------------------
\* Useful Unchanged shortcuts
unchanged_M == UNCHANGED <<oMsgs>>
unchanged_m == UNCHANGED <<mEID, mAliveNodes>>
unchanged_t == UNCHANGED <<tState,  tVersion, tRcvACKs>>
unchanged_r == UNCHANGED <<rID, rTS, rEID, rType>>
unchanged_c == UNCHANGED <<committedREQs, committedRTS>>
unchanged_o == UNCHANGED <<oState, oDriver, oVector, oRcvACKs, oTS>>
unchanged_mc    == unchanged_m    /\ unchanged_c 
unchanged_mtc   == unchanged_mc   /\ unchanged_t  
unchanged_mtr   == unchanged_m    /\ unchanged_t  /\ unchanged_r
unchanged_Mrc   == unchanged_r    /\ unchanged_c  /\ unchanged_M
unchanged_mrco  == unchanged_mc   /\ unchanged_r  /\ unchanged_o
unchanged_mtco  == unchanged_mtc  /\ unchanged_o 
unchanged_mtrc  == unchanged_mtc  /\ unchanged_r 
unchanged_Mtrc  == unchanged_Mrc  /\ unchanged_t 
unchanged_Mmrc  == unchanged_Mrc  /\ unchanged_m
unchanged_mtrco == unchanged_mtrc /\ unchanged_o 
unchanged_Mmrco == unchanged_mrco /\ unchanged_M
unchanged_Mmtrc == unchanged_mtrc /\ unchanged_M
 
                              
-------------------------------------------------------------------------------------
\* Type definitions
Type_oTS     == [ver: 0..O_MAX_VERSION, tb: LB_NODES_0]
Type_rTS     == [ver: 0..O_MAX_VERSION, tb: APP_NODES_0]
Type_tState  == {"valid", "invalid", "write"} \* readers can be in valid and invalid and owner in valid and write
Type_oState  == {"valid", "invalid", "drive", "request"} \* all nodes start from valid
Type_rType   == {"add-owner", "change-owner", "add-reader", "rm-reader", "NOOP"}
Type_oVector == [readers:  SUBSET APP_NODES, owner: APP_NODES_0]

Type_oMessage ==  \* Msgs exchanged by the sharding protocol 
    [type: {"REQ"},     rTS      : Type_rTS,
                        rID      : Nat,
                        rType    : Type_rType,
                        epochID  : 0..O_MAX_FAILURES] 
    \union
    [type: {"NACK"},    rTS      : Type_rTS,
                        rID      : Nat]
    \union
    [type: {"S_INV"},   sender   : O_NODES,
                        driver   : O_NODES,
                        rTS      : Type_rTS,
                        rID      : Nat,
                        oTS      : Type_oTS,
                        oVector  : Type_oVector,
                        rType    : Type_rType,
                        epochID  : 0..O_MAX_FAILURES] 
    \union
    [type: {"S_ACK"},   sender   : O_NODES,
                        oTS      : Type_oTS,
                        tVersion : 0..O_MAX_DATA_VERSION, \* emulates data send as well
                        epochID  : 0..O_MAX_FAILURES]
    \union
    [type: {"RESP"},    oVector  : Type_oVector,
                        oTS      : Type_oTS,
                        rTS      : Type_rTS,
\*                        preOwner , \* pre-request owner is not needed for model check (since we model bcast messages)
                        tVersion : 0..O_MAX_DATA_VERSION,
                        epochID  : 0..O_MAX_FAILURES]
    \union
    [type: {"S_VAL"},   oTS      : Type_oTS,
                        epochID  : 0..O_MAX_FAILURES]


Type_tMessage ==  \* msgs exchanged by the transactional reliable commit protocol
    [type: {"T_INV", "T_ACK", "T_VAL"},   tVersion : Nat,
                                          sender   : O_NODES,
                                          epochID  : 0..O_MAX_FAILURES]
                        
   
-------------------------------------------------------------------------------------
\* Type check and initialization
   
OTypeOK ==  \* The type correctness invariant
    /\ oTS           \in [O_NODES   -> Type_oTS]
    /\ oState        \in [O_NODES   -> Type_oState]
    /\ oDriver       \in [O_NODES   -> O_NODES_0]
    /\ oVector       \in [O_NODES   -> Type_oVector]
    /\ \A n \in O_NODES: oRcvACKs[n] \subseteq (O_NODES \ {n})
    /\ rTS           \in [O_NODES   -> Type_rTS]
    /\ rID           \in [O_NODES   -> 0..O_MAX_VERSION]
    /\ rType         \in [O_NODES   -> Type_rType]
    /\ rEID          \in [O_NODES   -> 0..(Cardinality(O_NODES) - 1)]
    /\ tVersion      \in [O_NODES   -> 0..O_MAX_DATA_VERSION]
    /\ tState        \in [O_NODES   -> Type_tState]
    /\ \A n \in O_NODES: tRcvACKs[n] \subseteq (O_NODES \ {n})
    /\ committedREQs \subseteq Type_oTS
    /\ committedRTS  \subseteq Type_rTS
    /\ oMsgs         \subseteq (Type_oMessage \union Type_tMessage)
    /\ mEID          \in 0..(Cardinality(O_NODES) - 1)
    /\ mAliveNodes   \subseteq O_NODES

OInit == \* The initial predicate
    /\ oTS           = [n \in O_NODES   |-> [ver |-> 0, tb |-> 0]]
    /\ oState        = [n \in O_NODES   |-> "valid"]
    /\ oDriver       = [n \in O_NODES   |-> 0]
    /\ oVector       = [n \in O_NODES   |-> [readers |-> {}, owner |-> 0]]
    /\ oRcvACKs      = [n \in O_NODES   |-> {}]
    /\ rTS           = [n \in O_NODES   |-> [ver |-> 0, tb |-> 0]]
    /\ rID           = [n \in O_NODES   |-> 0]
    /\ rEID          = [n \in O_NODES   |-> 0]
    /\ rType         = [n \in O_NODES   |-> "NOOP"]
    /\ tVersion      = [n \in O_NODES   |-> 0]
    /\ tState        = [n \in O_NODES   |-> "valid"]
    /\ tRcvACKs      = [n \in O_NODES   |-> {}]
    /\ committedRTS  = {} 
    /\ committedREQs = {} 
    /\ oMsgs         = {}
    /\ mEID          = 0
    /\ mAliveNodes   = O_NODES

Min(S) == CHOOSE x \in S: \A y \in S \ {x}: y > x
set_wo_min(S) == S \ {Min(S)}
              
\* First Command executed once after OInit to initialize owner/readers and oVector state
OInit_min_owner_rest_readers ==
    /\ \A x \in O_NODES: tVersion[x] = 0
    /\ tVersion' = [n \in O_NODES |-> IF n \in LB_NODES THEN 0 ELSE 1]
    /\ oVector'  = [n \in O_NODES |-> IF n \in set_wo_min(APP_NODES)
                                      THEN oVector[n]
                                      ELSE [readers |-> set_wo_min(APP_NODES), 
                                            owner   |-> Min(APP_NODES)]]
    /\ unchanged_Mmrc 
    /\ UNCHANGED <<tState, oState, oDriver, oRcvACKs, oTS, tRcvACKs>>

-------------------------------------------------------------------------------------
\* Helper functions
has_data(n) == tVersion[n] > 0
has_valid_data(n) == /\ has_data(n)
                     /\ tState[n] = "valid"

is_owner(n) ==  /\ has_data(n)
                /\ oVector[n].owner = n

is_valid_owner(n) ==  /\ is_owner(n)
                      /\ oState[n] = "valid"

is_reader(n) == /\ has_data(n)
                /\ ~is_owner(n)
                /\ n \notin LB_NODES

is_live_arbiter(n) ==  \/ n \in LB_LIVE_NODES
                       \/ is_owner(n)

is_valid_live_arbiter(n) ==  /\ is_live_arbiter(n)
                             /\ oState[n] = "valid"

is_requester(n) == 
    /\ n \in APP_LIVE_NODES
    /\ ~is_owner(n)

is_valid_requester(n) == 
    /\ is_requester(n)
    /\ oState[n] = "valid"

is_in_progress_requester(n) == 
    /\ is_requester(n)
    /\ oState[n] = "request"

requester_is_alive(n) == rTS[n].tb \in mAliveNodes

-------------------------------------------------------------------------------------
\* Timestamp Comparison Helper functions
is_equalTS(ts1, ts2) ==  
    /\ ts1.ver = ts2.ver
    /\ ts1.tb  = ts2.tb

is_greaterTS(ts1, ts2) == 
    \/ ts1.ver > ts2.ver
    \/ /\  ts1.ver = ts2.ver
       /\  ts1.tb  > ts2.tb

is_greatereqTS(ts1, ts2) == 
    \/ is_equalTS(ts1, ts2)
    \/ is_greaterTS(ts1, ts2)

is_smallerTS(ts1, ts2) == ~is_greatereqTS(ts1, ts2)

-------------------------------------------------------------------------------------
\* Request type Helper functions
is_non_sharing_req(n) == (rType[n] = "add-owner" \/ rType[n] = "add-reader")

\* Post o_vector based on request type and r (requester or 0 if requester is not alive)
post_oVec(n, r, pre_oVec) == 
    IF (rType[n] = "add-owner" \/ rType[n] = "change-owner")
    THEN [owner   |-> r,
          readers |-> (pre_oVec.readers \union {pre_oVec.owner}) \ {r, 0}]
    ELSE [owner   |-> pre_oVec.owner, 
          readers |-> IF rType[n] = "remove-reader"
                         THEN pre_oVec.readers \ {r, 0}
                         ELSE \* rType[n] = "add-reader"
                             (pre_oVec.readers \union {r}) \ {0}]

 
-------------------------------------------------------------------------------------
\* Message Helper functions

\* Used only to emulate FIFO REQ channels (and not re-execute already completed REQs)
not_completed_rTS(r_ts) == \A c_rTS \in  committedRTS: c_rTS # r_ts

\* Messages in oMsgs are only appended to this variable (not removed once delivered) 
\* intentionally to check protocols tolerance in dublicates and reorderings 
send_omsg(m) == oMsgs' = oMsgs \union {m}  

o_send_req(r_ts, r_id, r_type) ==  
        send_omsg([type        |-> "REQ",
                   rTS         |-> r_ts, 
                   rID         |-> r_id, 
                   rType       |-> r_type, 
                   epochID     |-> mEID ])              

o_send_nack(r_ts, r_id) ==  
        send_omsg([type        |-> "NACK",
                   rTS         |-> r_ts, 
                   rID         |-> r_id])              

o_send_inv(sender, driver, o_ts, o_vec, r_ts, r_id, r_type) ==  
        send_omsg([type        |-> "S_INV",
                   sender      |-> sender,
                   driver      |-> driver,
                   oTS         |-> o_ts, 
                   oVector     |-> o_vec, 
                   rTS         |-> r_ts, 
                   rID         |-> r_id, 
                   rType       |-> r_type,              
                   epochID     |-> mEID ])              

o_send_ack(sender, o_ts, t_version) ==  
        send_omsg([type        |-> "S_ACK",
                   sender      |-> sender,
                   oTS         |-> o_ts, 
                   tVersion    |-> t_version,              
                   epochID     |-> mEID ])              

o_send_resp(r_ts, o_ts, o_vec, t_version) ==  
        send_omsg([type        |-> "RESP",
                   oVector     |-> o_vec,
                   oTS         |-> o_ts, 
                   rTS         |-> r_ts, 
                   tVersion    |-> t_version,              
                   epochID     |-> mEID ])              

o_send_val(o_ts) ==  
        send_omsg([type        |-> "S_VAL",
                   oTS         |-> o_ts,              
                   epochID     |-> mEID    ])
                   
\* Operators to check received messages (m stands for message)
o_rcv_req(m) == 
    /\ m.type = "REQ"
    /\ m.epochID = mEID
    /\ not_completed_rTS(m.rTS)

o_rcv_nack(m, receiver) ==
    /\ m.type = "NACK"
    /\ m.rTS  = rTS[receiver]
    /\ m.rID  = rID[receiver]

o_rcv_resp(m, receiver)  ==
    /\ m.type    = "RESP"
    /\ m.epochID = mEID
    /\ m.rTS     = rTS[receiver]

o_rcv_inv(m, receiver)  ==
    /\ m.type     = "S_INV"
    /\ m.epochID  = mEID
    /\ m.sender   # receiver

o_rcv_inv_equal_ts(m, receiver)  ==
    /\ o_rcv_inv(m, receiver)
    /\ is_equalTS(m.oTS, oTS[receiver])

o_rcv_inv_smaller_ts(m, receiver)  ==
    /\ o_rcv_inv(m, receiver)
    /\ is_smallerTS(m.oTS, oTS[receiver])

o_rcv_inv_greater_ts(m, receiver)  ==
    /\ o_rcv_inv(m, receiver)
    /\ is_greaterTS(m.oTS, oTS[receiver])

o_rcv_inv_greatereq_ts(m, receiver)  ==
    /\ o_rcv_inv(m, receiver)
    /\ ~is_smallerTS(m.oTS, oTS[receiver])

o_rcv_ack(m, receiver)  ==
    /\ m.type     = "S_ACK"
    /\ m.epochID  = mEID
    /\ m.sender   # receiver
    /\ oState[receiver] = "drive"
    /\ m.sender   \notin oRcvACKs[receiver]
    /\ is_equalTS(m.oTS, oTS[receiver])
    
o_rcv_val(m, receiver)  ==
    /\ m.type = "S_VAL"
    /\ m.epochID  = mEID
    /\ oState[receiver] # "valid"
    /\ is_equalTS(m.oTS, oTS[receiver])
    
    
\* Used to not re-issue messages that already exists (and bound the state space)
msg_not_exists(o_rcv_msg(_, _), receiver) ==
        ~\E mm \in oMsgs: o_rcv_msg(mm, receiver)
    


rcved_acks_from_set(n, set) ==  set \subseteq oRcvACKs[n]

\* Check if all acknowledgments from arbiters have been received                                                  
has_rcved_all_ACKs(n) == 
    /\ rEID[n] = mEID
    /\ IF     oVector[n].owner  # 0
       THEN   rcved_acks_from_set(n, {oVector[n].owner} \union LB_LIVE_ARBITERS(n)) 
       ELSE \/ /\ ~requester_is_alive(n)
               /\  rcved_acks_from_set(n, LB_LIVE_ARBITERS(n))
            \/ /\  oVector[n].readers # {}
               /\  \E x \in oVector[n].readers: rcved_acks_from_set(n, {x} \union LB_LIVE_ARBITERS(n)) 
-------------------------------------------------------------------------------------
\* message helper functions related to transactions
t_send(n, msg_type, t_ver) ==
        send_omsg([type        |-> msg_type,
                   tVersion    |-> t_ver,              
                   sender      |-> n,
                   epochID     |-> mEID    ])
 
t_rcv_inv(m, receiver)  ==
    /\ m.type     = "T_INV"
    /\ m.epochID  = mEID
    /\ m.sender   # receiver

t_rcv_ack(m, receiver)  ==
    /\ m.type     = "T_ACK"
    /\ m.epochID  = mEID
    /\ m.sender   # receiver
    /\ tState[receiver] = "write"
    /\ m.sender   \notin tRcvACKs[receiver]
    /\ m.tVersion = tVersion[receiver]
    
t_rcv_val(m, receiver)  ==
    /\ m.type = "T_VAL"
    /\ m.epochID  = mEID
    /\ tState[receiver] # "valid"
    /\ m.tVersion = tVersion[receiver]
       
-------------------------------------------------------------------------------------
\* Protocol Invariants: 

\* Valid data are consistent 
CONSISTENT_DATA ==
    \A k,n \in APP_LIVE_NODES: \/ ~has_valid_data(k)
                               \/ ~has_valid_data(n)
                               \/ tVersion[n] = tVersion[k]

\* Amongst concurrent sharing requests only one succeeds 
\* The invariant that an we cannot have two REQs committed with same versions 
\* (i.e., that read and modified the same sharing vector)
ONLY_ONE_CONC_REQ_COMMITS ==  
    \A x,y \in committedREQs: \/ x.ver # y.ver
                              \/ x.tb = y.tb

\* There is always at most one valid owner
AT_MOST_ONE_OWNER == 
    \A n,m \in mAliveNodes: \/ ~is_valid_owner(n)
                            \/ ~is_valid_owner(m)
                            \/ m = n

\* Valid owner has the most up-to-date data and version among live replicas
OWNER_LATEST_DATA == 
    \A o,k \in mAliveNodes: \/ ~is_valid_owner(o)
                            \/ ~has_data(o)
                            \/ tVersion[o] >= tVersion[k]

\* All valid sharers (LB + owner) agree on their sharing vectors (and TS)
CONSISTENT_SHARERS == 
    \A k,n \in mAliveNodes: \/ ~is_valid_live_arbiter(n)
                            \/ ~is_valid_live_arbiter(k)
                            \/ /\ oTS[n] = oTS[k]
                               /\ oVector[n] = oVector[k]


CONSISTENT_OVECTORS_Fwd == 
    \A n \in mAliveNodes: \/ ~is_valid_live_arbiter(n)
                          \/ /\ \A r \in oVector[n].readers: 
                                /\ has_data(r)
                                /\ ~is_valid_owner(r)
                             /\ \/ oVector[n].owner = 0 
                                \/ is_owner(oVector[n].owner)

CONSISTENT_OVECTORS_Reverse_owner == 
    \A o,n \in mAliveNodes: \/ ~is_valid_owner(o)
                            \/ ~is_valid_live_arbiter(n)
                            \/ oVector[n].owner = o

CONSISTENT_OVECTORS_Reverse_readers == 
    \A r,n \in mAliveNodes: \/ ~is_reader(r)
                            \/ ~is_valid_live_arbiter(n)
                            \/ r \in oVector[n].readers 

\* The owner and readers are always correctly reflected by any valid sharing vectors
CONSISTENT_OVECTORS ==                           
    /\ CONSISTENT_OVECTORS_Fwd
    /\ CONSISTENT_OVECTORS_Reverse_owner 
    /\ CONSISTENT_OVECTORS_Reverse_readers 

=============================================================================
