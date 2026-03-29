fn main() {
    use cadical_sys::Status;
    use cadical_sys::CaDiCal;
    {
        // Create a new solver instance
        let mut solver = CaDiCal::new();

        // Add clauses (representing a simple propositional logic problem)
        // For example, (x1 OR x2) AND (NOT x1 OR x3) AND (NOT x2 OR NOT x3)
        solver.clause2(1, 2);    // x1 OR x2
        solver.clause2(-1, 3);   // NOT x1 OR x3
        solver.clause2(-2, -3);  // NOT x2 OR NOT x3

        // Solve the problem
        let status = solver.solve();
        match status {
            Status::SATISFIABLE => {
                // Get variable assignments
                println!("x1: {}", solver.val(1));
                println!("x2: {}", solver.val(2));
                println!("x3: {}", solver.val(3));
            },
            Status::UNSATISFIABLE => println!("No solution exists"),
            Status::UNKNOWN => println!("Solution status unknown")
        }
    }

    {
        let mut solver = CaDiCal::new();

        // Configure the solver
        solver.configure("plain".to_string());

        // Set some options
        solver.set("verbose".to_string(), 1);

        // Add complex clauses
        solver.clause3(1, 2, 3);  // x1 OR x2 OR x3
        solver.clause3(-1, -2, -3);  // NOT x1 OR NOT x2 OR NOT x3

        // Make assumptions
        solver.assume(1);  // Assume x1 is true

        // Solve with assumptions
        let status = solver.solve();

        // Check solving results
        if status == Status::SATISFIABLE {
            // Interact with solved model
            let num_vars = solver.vars();
            for var in 1..=num_vars {
                println!("Variable {}: {}", var, solver.val(var));
            }
        }
    }
}
