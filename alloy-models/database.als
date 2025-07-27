// Simple Database Model

module database

// Database tables
sig Table {
    name: one String
}

// Table rows
sig Row {
    table: one Table,
    id: one Int
}

// Users table
one sig Users extends Table {}

// Orders table  
one sig Orders extends Table {}

// Foreign key relationship
sig OrderUserLink {
    order_row: one Row,
    user_row: one Row
}

// Basic constraints
fact DatabaseRules {
    // Users table setup
    Users.name = "users"
    
    // Orders table setup
    Orders.name = "orders"
    
    // Unique row IDs within each table
    all t: Table |
        all disj r1, r2: Row |
            r1.table = t and r2.table = t implies r1.id != r2.id
    
    // Foreign key integrity
    all link: OrderUserLink |
        link.order_row.table = Orders and
        link.user_row.table = Users
}

// Example with data
pred DatabaseExample {
    some user_row, order_row: Row |
    some link: OrderUserLink | {
        user_row.table = Users
        user_row.id = 1
        
        order_row.table = Orders
        order_row.id = 101
        
        link.order_row = order_row
        link.user_row = user_row
    }
}

run DatabaseExample for 4