// Simple Consensus Model

module consensus

// Nodes in the system
sig Node {
    id: one Int,
    is_leader: one Bool,
    term: one Int
}

// Messages between nodes
sig Vote {
    from: one Node,
    for: one Node,
    term: one Int
}

// Basic constraints
fact BasicConsensus {
    // Unique node IDs
    all disj n1, n2: Node | n1.id != n2.id
    
    // At most one leader per term
    all t: Int |
        lone n: Node | n.is_leader = True and n.term = t
    
    // Nodes vote in their current term
    all v: Vote | v.term = v.from.term
}

// Leader election
pred LeaderElection {
    some leader, follower1, follower2: Node |
    some vote1, vote2: Vote | {
        // Three nodes
        leader.id = 1
        follower1.id = 2
        follower2.id = 3
        
        // Same term
        leader.term = follower1.term
        leader.term = follower2.term
        
        // Leader gets votes
        vote1.from = follower1
        vote1.for = leader
        vote2.from = follower2
        vote2.for = leader
        
        // Leader status
        leader.is_leader = True
        follower1.is_leader = False
        follower2.is_leader = False
    }
}

run LeaderElection for 5