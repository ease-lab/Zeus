--------------------------- MODULE ZeusOwnershipMeta ---------------------------

EXTENDS     Integers, FiniteSets

CONSTANTS   \* LB_NODES and APP_NODES must not intersect and neither should contain 0.
            LB_NODES, 
            APP_NODES,
            S_MAX_VERSION,
            S_MAX_FAILURES,
            S_MAX_DATA_VERSION
                      

VARIABLES   \* variable prefixes --> s: sharding, r: request, t: transactional, m: membership 
            \* VECTORS indexed by node_id
            sTS,
            sState,
            sDriver,
            sVector,    \* No readers/owner: .readers = {} / .owner = 0 
            sRcvACKs,
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
            sMsgs,
            mAliveNodes,  \* membership
            mEID,         \* membership epoch id
            committedREQs, \* only to check invariant that exactly one of concurrent REQs is committed
            committedRTS  \* only to emulate FIFO REQ channels (i.e., do not re execute same client requests)

vars == << sTS, sState, sDriver, sVector, sRcvACKs, rTS, rID, rType, rEID,        
           tState, tVersion, tRcvACKs, sMsgs, mAliveNodes, mEID, committedREQs, committedRTS>>

\* Helper operators 
S_NODES        == LB_NODES  \union APP_NODES
S_NODES_0      == S_NODES   \union {0}
LB_NODES_0     == LB_NODES  \union {0}
APP_NODES_0    == APP_NODES \union {0} 
LB_LIVE_NODES  == LB_NODES  \intersect mAliveNodes
APP_LIVE_NODES == APP_NODES \intersect mAliveNodes
LB_LIVE_ARBITERS(driver) == LB_LIVE_NODES \ {driver} \* all arbiters except driver and owner

ASSUME LB_NODES \intersect APP_NODES = {}
ASSUME \A k \in S_NODES: k # 0 \* we use 0 as the default noop

-------------------------------------------------------------------------------------
\* Useful Unchanged shortcuts
unchanged_M == UNCHANGED <<sMsgs>>
unchanged_m == UNCHANGED <<mEID, mAliveNodes>>
unchanged_t == UNCHANGED <<tState,  tVersion, tRcvACKs>>
unchanged_r == UNCHANGED <<rID, rTS, rEID, rType>>
unchanged_c == UNCHANGED <<committedREQs, committedRTS>>
unchanged_s == UNCHANGED <<sState, sDriver, sVector, sRcvACKs, sTS>>
unchanged_mc    == unchanged_m    /\ unchanged_c 
unchanged_mtc   == unchanged_mc   /\ unchanged_t  
unchanged_mtr   == unchanged_m    /\ unchanged_t  /\ unchanged_r
unchanged_Mrc   == unchanged_r    /\ unchanged_c  /\ unchanged_M
unchanged_mrcs  == unchanged_mc   /\ unchanged_r  /\ unchanged_s
unchanged_mtcs  == unchanged_mtc  /\ unchanged_s 
unchanged_mtrc  == unchanged_mtc  /\ unchanged_r 
unchanged_Mtrc  == unchanged_Mrc  /\ unchanged_t 
unchanged_Mmrc  == unchanged_Mrc  /\ unchanged_m
unchanged_mtrcs == unchanged_mtrc /\ unchanged_s 
unchanged_Mmrcs == unchanged_mrcs /\ unchanged_M
unchanged_Mmtrc == unchanged_mtrc /\ unchanged_M
 
                              
-------------------------------------------------------------------------------------
\* Type definitions
Type_sTS     == [ver: 0..S_MAX_VERSION, tb: LB_NODES_0]
Type_rTS     == [ver: 0..S_MAX_VERSION, tb: APP_NODES_0]
Type_tState  == {"valid", "invalid", "write"} \* readers can be in valid and invalid and owner in valid and write
Type_sState  == {"valid", "invalid", "drive", "request"} \* all nodes start from valid
Type_rType   == {"add-owner", "change-owner", "add-reader", "rm-reader", "NOOP"}
Type_sVector == [readers:  SUBSET APP_NODES, owner: APP_NODES_0]

Type_sMessage ==  \* Msgs exchanged by the sharding protocol 
    [type: {"REQ"},     rTS      : Type_rTS,
                        rID      : Nat,
                        rType    : Type_rType,
                        epochID  : 0..S_MAX_FAILURES] 
    \union
    [type: {"NACK"},    rTS      : Type_rTS,
                        rID      : Nat]
    \union
    [type: {"S_INV"},   sender   : S_NODES,
                        driver   : S_NODES,
                        rTS      : Type_rTS,
                        rID      : Nat,
                        sTS      : Type_sTS,
                        sVector  : Type_sVector,
                        rType    : Type_rType,
                        epochID  : 0..S_MAX_FAILURES] 
    \union
    [type: {"S_ACK"},   sender   : S_NODES,
                        sTS      : Type_sTS,
                        tVersion : 0..S_MAX_DATA_VERSION, \* emulates data send as well
                        epochID  : 0..S_MAX_FAILURES]
    \union
    [type: {"RESP"},    sVector  : Type_sVector,
                        sTS      : Type_sTS,
                        rTS      : Type_rTS,
\*                        preOwner , \* pre-request owner is not needed for model check (since we model bcast messages)
                        tVersion : 0..S_MAX_DATA_VERSION,
                        epochID  : 0..S_MAX_FAILURES]
    \union
    [type: {"S_VAL"},   sTS      : Type_sTS,
\*                        sVector  : Type_sVector,     TBD:post-svec
                        epochID  : 0..S_MAX_FAILURES]


Type_tMessage ==  \* msgs exchanged by the transactional protocol
    [type: {"T_INV", "T_ACK", "T_VAL"},   tVersion : Nat,
                                          sender   : S_NODES,
                                          epochID  : 0..S_MAX_FAILURES]
                        
   
-------------------------------------------------------------------------------------
\* Type check and initialization
   
STypeOK ==  \* The type correctness invariant
    /\ sTS           \in [S_NODES   -> Type_sTS]
    /\ sState        \in [S_NODES   -> Type_sState]
    /\ sDriver       \in [S_NODES   -> S_NODES_0]
    /\ sVector       \in [S_NODES   -> Type_sVector]
    /\ \A n \in S_NODES: sRcvACKs[n] \subseteq (S_NODES \ {n})
    /\ rTS           \in [S_NODES   -> Type_rTS]
    /\ rID           \in [S_NODES   -> 0..S_MAX_VERSION]
    /\ rType         \in [S_NODES   -> Type_rType]
    /\ rEID          \in [S_NODES   -> 0..(Cardinality(S_NODES) - 1)]
    /\ tVersion      \in [S_NODES   -> 0..S_MAX_DATA_VERSION]
    /\ tState        \in [S_NODES   -> Type_tState]
    /\ \A n \in S_NODES: tRcvACKs[n] \subseteq (S_NODES \ {n})
    /\ committedREQs \subseteq Type_sTS
    /\ committedRTS  \subseteq Type_rTS
    /\ sMsgs         \subseteq (Type_sMessage \union Type_tMessage)
    /\ mEID          \in 0..(Cardinality(S_NODES) - 1)
    /\ mAliveNodes   \subseteq S_NODES

SInit == \* The initial predicate
    /\ sTS           = [n \in S_NODES   |-> [ver |-> 0, tb |-> 0]]
    /\ sState        = [n \in S_NODES   |-> "valid"]
    /\ sDriver       = [n \in S_NODES   |-> 0]
    /\ sVector       = [n \in S_NODES   |-> [readers |-> {}, owner |-> 0]]
    /\ sRcvACKs      = [n \in S_NODES   |-> {}]
    /\ rTS           = [n \in S_NODES   |-> [ver |-> 0, tb |-> 0]]
    /\ rID           = [n \in S_NODES   |-> 0]
    /\ rEID          = [n \in S_NODES   |-> 0]
    /\ rType         = [n \in S_NODES   |-> "NOOP"]
    /\ tVersion      = [n \in S_NODES   |-> 0]
    /\ tState        = [n \in S_NODES   |-> "valid"]
    /\ tRcvACKs      = [n \in S_NODES   |-> {}]
    /\ committedRTS  = {} 
    /\ committedREQs = {} 
    /\ sMsgs         = {}
    /\ mEID          = 0
    /\ mAliveNodes   = S_NODES

Min(S) == CHOOSE x \in S: \A y \in S \ {x}: y > x
set_wo_min(S) == S \ {Min(S)}
              
\* First Command executed once after SInit to initialize owner/readers and sVector state
SInit_min_owner_rest_readers ==
    /\ \A x \in S_NODES: tVersion[x] = 0
    /\ tVersion' = [n \in S_NODES |-> IF n \in LB_NODES THEN 0 ELSE 1]
    /\ sVector'  = [n \in S_NODES |-> IF n \in set_wo_min(APP_NODES)
                                      THEN sVector[n]
                                      ELSE [readers |-> set_wo_min(APP_NODES), 
                                            owner   |-> Min(APP_NODES)]]
    /\ unchanged_Mmrc 
    /\ UNCHANGED <<tState, sState, sDriver, sRcvACKs, sTS, tRcvACKs>>

-------------------------------------------------------------------------------------
\* Helper functions
has_data(n) == tVersion[n] > 0
has_valid_data(n) == /\ has_data(n)
                     /\ tState[n] = "valid"

is_owner(n) ==  /\ has_data(n)
                /\ sVector[n].owner = n

is_valid_owner(n) ==  /\ is_owner(n)
                      /\ sState[n] = "valid"

is_reader(n) == /\ has_data(n)
                /\ ~is_owner(n)
                /\ n \notin LB_NODES

is_live_arbiter(n) ==  \/ n \in LB_LIVE_NODES
                       \/ is_owner(n)

is_valid_live_arbiter(n) ==  /\ is_live_arbiter(n)
                             /\ sState[n] = "valid"

is_requester(n) == 
    /\ n \in APP_LIVE_NODES
    /\ ~is_owner(n)

is_valid_requester(n) == 
    /\ is_requester(n)
    /\ sState[n] = "valid"

is_in_progress_requester(n) == 
    /\ is_requester(n)
    /\ sState[n] = "request"

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

\* Post s_vector based on request type and r (requester or 0 if requester is not alive)
post_sVec(n, r, pre_sVec) == 
    IF (rType[n] = "add-owner" \/ rType[n] = "change-owner")
    THEN [owner   |-> r,
          readers |-> (pre_sVec.readers \union {pre_sVec.owner}) \ {r, 0}]
    ELSE [owner   |-> pre_sVec.owner, 
          readers |-> IF rType[n] = "remove-reader"
                         THEN pre_sVec.readers \ {r, 0}
                         ELSE \* rType[n] = "add-reader"
                             (pre_sVec.readers \union {r}) \ {0}]

 
-------------------------------------------------------------------------------------
\* Message Helper functions

\* Used only to emulate FIFO REQ channels (and not re-execute already completed REQs)
not_completed_rTS(r_ts) == \A c_rTS \in  committedRTS: c_rTS # r_ts

\* Messages in sMsgs are only appended to this variable (not removed once delivered) 
\* intentionally to check protocols tolerance in dublicates and reorderings 
send_smsg(m) == sMsgs' = sMsgs \union {m}  

s_send_req(r_ts, r_id, r_type) ==  
        send_smsg([type        |-> "REQ",
                   rTS         |-> r_ts, 
                   rID         |-> r_id, 
                   rType       |-> r_type, 
                   epochID     |-> mEID ])              

s_send_nack(r_ts, r_id) ==  
        send_smsg([type        |-> "NACK",
                   rTS         |-> r_ts, 
                   rID         |-> r_id])              

s_send_inv(sender, driver, s_ts, s_vec, r_ts, r_id, r_type) ==  
        send_smsg([type        |-> "S_INV",
                   sender      |-> sender,
                   driver      |-> driver,
                   sTS         |-> s_ts, 
                   sVector     |-> s_vec, 
                   rTS         |-> r_ts, 
                   rID         |-> r_id, 
                   rType       |-> r_type,              
                   epochID     |-> mEID ])              

s_send_ack(sender, s_ts, t_version) ==  
        send_smsg([type        |-> "S_ACK",
                   sender      |-> sender,
                   sTS         |-> s_ts, 
                   tVersion    |-> t_version,              
                   epochID     |-> mEID ])              

s_send_resp(r_ts, s_ts, s_vector, t_version) ==  
        send_smsg([type        |-> "RESP",
                   sVector     |-> s_vector,
                   sTS         |-> s_ts, 
                   rTS         |-> r_ts, 
                   tVersion    |-> t_version,              
                   epochID     |-> mEID ])              

\* TBD:post-svec
\*s_send_val(s_ts, s_vector) ==  
s_send_val(s_ts) ==  
        send_smsg([type        |-> "S_VAL",
                   sTS         |-> s_ts,              
\*                   sVector     |-> s_vector, \* TBD:post-svec
                   epochID     |-> mEID    ])
                   
\* Operators to check received messages (m stands for message)
s_rcv_req(m) == 
    /\ m.type = "REQ"
    /\ m.epochID = mEID
    /\ not_completed_rTS(m.rTS)

s_rcv_nack(m, receiver) ==
    /\ m.type = "NACK"
    /\ m.rTS  = rTS[receiver]
    /\ m.rID  = rID[receiver]

s_rcv_resp(m, receiver)  ==
    /\ m.type    = "RESP"
    /\ m.epochID = mEID
    /\ m.rTS     = rTS[receiver]

s_rcv_inv(m, receiver)  ==
    /\ m.type     = "S_INV"
    /\ m.epochID  = mEID
    /\ m.sender   # receiver

s_rcv_inv_equal_ts(m, receiver)  ==
    /\ s_rcv_inv(m, receiver)
    /\ is_equalTS(m.sTS, sTS[receiver])

s_rcv_inv_smaller_ts(m, receiver)  ==
    /\ s_rcv_inv(m, receiver)
    /\ is_smallerTS(m.sTS, sTS[receiver])

s_rcv_inv_greater_ts(m, receiver)  ==
    /\ s_rcv_inv(m, receiver)
    /\ is_greaterTS(m.sTS, sTS[receiver])

s_rcv_inv_greatereq_ts(m, receiver)  ==
    /\ s_rcv_inv(m, receiver)
    /\ ~is_smallerTS(m.sTS, sTS[receiver])

s_rcv_ack(m, receiver)  ==
    /\ m.type     = "S_ACK"
    /\ m.epochID  = mEID
    /\ m.sender   # receiver
    /\ sState[receiver] = "drive"
    /\ m.sender   \notin sRcvACKs[receiver]
    /\ is_equalTS(m.sTS, sTS[receiver])
    
s_rcv_val(m, receiver)  ==
    /\ m.type = "S_VAL"
    /\ m.epochID  = mEID
    /\ sState[receiver] # "valid"
    /\ is_equalTS(m.sTS, sTS[receiver])
    
    
\* Used to not re-issue messages that already exists (and bound the state space)
msg_not_exists(s_rcv_msg(_, _), receiver) ==
        ~\E mm \in sMsgs: s_rcv_msg(mm, receiver)
    


rcved_acks_from_set(n, set) ==  set \subseteq sRcvACKs[n]

\* Check if all acknowledgments from arbiters have been received                                                  
has_rcved_all_ACKs(n) == 
    /\ rEID[n] = mEID
    /\ IF     sVector[n].owner  # 0
       THEN   rcved_acks_from_set(n, {sVector[n].owner} \union LB_LIVE_ARBITERS(n)) 
       ELSE \/ /\ ~requester_is_alive(n)
               /\  rcved_acks_from_set(n, LB_LIVE_ARBITERS(n))
            \/ /\  sVector[n].readers # {}
               /\  \E x \in sVector[n].readers: rcved_acks_from_set(n, {x} \union LB_LIVE_ARBITERS(n)) 
-------------------------------------------------------------------------------------
\* message helper functions related to transactions
t_send(n, msg_type, t_ver) ==
        send_smsg([type        |-> msg_type,
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
    /\ m.type = "S_VAL"
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
                            \/ /\ sTS[n] = sTS[k]
                               /\ sVector[n] = sVector[k]


CONSISTENT_SVECTORS_Fwd == 
    \A n \in mAliveNodes: \/ ~is_valid_live_arbiter(n)
                          \/ /\ \A r \in sVector[n].readers: 
                                /\ has_data(r)
                                /\ ~is_valid_owner(r)
                             /\ \/ sVector[n].owner = 0 
                                \/ is_owner(sVector[n].owner)

CONSISTENT_SVECTORS_Reverse_owner == 
    \A o,n \in mAliveNodes: \/ ~is_valid_owner(o)
                            \/ ~is_valid_live_arbiter(n)
                            \/ sVector[n].owner = o

CONSISTENT_SVECTORS_Reverse_readers == 
    \A r,n \in mAliveNodes: \/ ~is_reader(r)
                            \/ ~is_valid_live_arbiter(n)
                            \/ r \in sVector[n].readers 

\* The owner and readers are always correctly reflected by any valid sharing vectors
CONSISTENT_SVECTORS ==                           
    /\ CONSISTENT_SVECTORS_Fwd
    /\ CONSISTENT_SVECTORS_Reverse_owner 
    /\ CONSISTENT_SVECTORS_Reverse_readers 

=============================================================================
