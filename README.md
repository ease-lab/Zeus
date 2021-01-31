# Zeus Transactional Protocols

<img align="left" height="130" src="https://github.com/akatsarakis/zeus-specification/blob/master/zeus.png">

*Zeus* is a datastore that offers fast locality-aware distributed transactions with strong consistency and availability. A brief description follows and more details can be found in the [Eurosys'21](https://2021.eurosys.org/) paper. 

This is the publicly available artifact repository supporting *Zeus*, which contains the specification of the two protocols that enable Zeus locality-aware reliable transactions; the *ownership protocol* and the *reliable commit protocol* of Zeus. The specifications are written in TLA+ and can be used to verify Zeus's correctness via model-checking.

##  Inspired by
Zeus protocols build on ideas of [Hermes](https://hermes-protocol.com/) and draws inspiration from cache coherence and hardware transactional memory exapting ideas to a replicated distributed setting for availability. Inspired concepts include the invalidation-based design of both proposed protocols and Zeus's approach to move objects and ensure exclusive write access (*ownership*) to the coordinator of a write transaction.

----
# Locality-aware reliable transactions  
Transactions in Zeus involve three main phases:
  - __Prepare & Execute__: Execute the transaction locally; <br />
  If *locality is not captured* (i.e., if accessing an object not local to the executor -- or missing exclussive write access for write transactions) 
 <br /> &rarr; the object (and/or permissions) are acquired via the __ownership protocol__ 
    - *Exclusive owner* guarantee: at any time, at most one node with exclusive write access (i.e., *owner*) to an object     
    - *Fast/slow-path* design: to acquire ownership (and data) in at most 1.5 RTT regardless of the requesting node in the absence of faults
    - *Fault-tolerant*: each ownership protocol step is idempotent to recover from faults
  - __Local Commit__: *Any* traditional single node (unreliable -- i.e., non-replicated) commit
  - __Reliable Commit__: Replicate updates to sharers for data availability: 
    - *Fast Commit*: 1RTT that is also pipelined to hide the latency
    - *Read-only optimized transactions*: strictly serializable and local from any replica
    - *Fault-tolerant*: each reliable commit step is idempotent to recover from faults 

## Properties and Invariants
__Faults__: The specification and model checking assumes that crash-stop node faults and message reorderings may occur.
Message losses in Zeus are handled via retransmissions. The exact failure model can be found in the paper. <br />
__Strong Consistency__: Zeus transactions guarantee the strongest consistency (i.e., are strictly serializable).<br />
__Invariants__: A list of model-checked invariants provided by the protocols follows
* Amongst concurrent ownership requests to the same object, at most one succeeds.
* At any time, there is at most one valid owner of an object.
* A valid owner of an object has the most up-to-date data and version among live replicas.
* All valid sharer vectors (stored by directory nodes and the owner) of an object agree on the object's sharers and ownership timestamp (o_ts).
* The owner and readers are always correctly reflected by all valid sharer vectors.  
* A replica found in the valid state stores the latest committed value of an object.

---- 

## Model checking
To model check the protocols, you need to download and install the TLA+ Toolbox so that you can run the *TLC* model checker using either the Reliable commit or ownership *TLA+* specifications. We next list the steps to model check Zeus's *reliable commit protocol* (model checking the ownership protocol is similar).
* __Prerequisites__: Any OS with Java 1.8 or later, to accommodate the *TLA+* Toolbox.
* __Download and install__ the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html).
* __Launch__ the TLA+ Toolbox.
* __Create a spec__: *File>Open Spec>Add New Spec...*; Browse and use *zeus/reliable_commit_protocol/ZeusReliableCommit.tla* as root module to finish.
* __Create a new Model__: Navigate to *TLC Model Checker>New model...*; and create a model with the name "reliable-commit-model".
* __Setup Behavior__: In *Model Overview* tab of the model, and under the *"What is the behavior spec?"* section, select *"Temporal formula"* and write *"Spec"*.
* __Setup Constants__: Then specify the values of declared constants (under *"What is the model?"* section). You may use low values for constants to check correctness without exploding the state space. An example configuration would be three nodes and maximum versions of two or three. To accomplish that, you would need to click on each constant and select the "ordinary assignment" option. Then fill the box for version and epoch constants (e.g., *R_MAX_VERSION*) with a small number (e.g., with *"2"* or *"3"*) and for any node related fields (e.g., *R_NODES*) with a set of nodes (e.g., *"{1,2,3}"* -- for three nodes).

### File Structure
* __The reliable commit specification__ is a single TLA+ module in *zeus/reliable_commit_protocol* folder.
* __The ownership specification__ is decoupled into three modules under the *zeus/ownership_protocol* folder for simplicity. *ZeusOwnership.tla* and *ZeusOwnershipMeta.tla* specify (and can be used to model check) the ownership protocol in the absence of faults. The specification with failures is built on top of those in the module *ZeusOwnershipFaults.tla*.

#### Caveats 
* The reliable commit specification does not include the pipelining optimization yet, and the ownership specification focuses on the slow-path for now -- which is mandatory to model check faults. 
* Apart from acquiring ownership, the ownership protocol can be utilized to handle other dynamic sharding actions (e.g., remove or add a reader replica) which were omitted from the paper. We may describe those in a separate online document if there is interest. 

----
### License
This work is freely distributed under the [Apache 2.0 License](https://www.apache.org/licenses/LICENSE-2.0 "Apache 2.0").  

### Contact
 Antonios Katsarakis: <a href="http://antonis.io/" title="Personal webpage" target="_blank">`antonis.io`</a> |  [`antoniskatsarakis@yahoo.com`](mailto:antoniskatsarakis@yahoo.com?subject=[GitHub]%20Zeus%20Specification "Email")

