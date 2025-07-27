// Simple File System Model

module filesystem

// Basic entities
sig User {
    name: one String
}

sig File {
    name: one String,
    owner: one User,
    readable: set User,
    writable: set User
}

sig Directory {
    name: one String,
    owner: one User,
    files: set File
}

// Root directory
one sig Root extends Directory {}

// Basic constraints
fact BasicStructure {
    // Every file is in exactly one directory
    all f: File | one d: Directory | f in d.files
    
    // Owner can always read and write their files
    all f: File | f.owner in f.readable and f.owner in f.writable
    
    // File names are unique within a directory
    all d: Directory | 
        all disj f1, f2: d.files | f1.name != f2.name
}

// Simple access control
pred canRead[u: User, f: File] {
    u in f.readable
}

pred canWrite[u: User, f: File] {
    u in f.writable
}

// Example scenario
pred SimpleExample {
    some alice, bob: User |
    some doc: File |
    some home: Directory | {
        alice.name = "alice"
        bob.name = "bob"
        doc.name = "document.txt"
        doc.owner = alice
        doc in home.files
        home.name = "home"
        
        // Alice can read/write, Bob can only read
        alice in doc.readable
        alice in doc.writable
        bob in doc.readable
        bob not in doc.writable
    }
}

run SimpleExample for 4