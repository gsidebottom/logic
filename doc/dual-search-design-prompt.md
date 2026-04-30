# Covers and Uncovered

## The prompt
> There is another way to compute satisfying and falsifying assignments and proving 
> than none exist (unsatisfiable and valid).  Let's take the satisfying case for 
> example where we look at paths in the NNF of the complement of the formula.
>
> We can process the complementary pairs in the matrix and keep track of which paths 
> they cover.  Picking complementary pairs which cover a lot of not yet covered paths 
> is a good heuristic if we can see which of the unprocessed complementary pairs are good next candidates for analysis.
>
> In parallel, we can search the currently unmarked paths for ones that aren't covered.  Many options are possible, basic depth nature or heuristic prod and sum order, from each end trying to meet in the middle, breadth first, best first and so on.  The uncovered path search can feed cover pairs as they are found into the parallel cover search process.
>
> In the end either all paths are determined to be covered and the formula is 
> unsatisfiable or uncovered paths are found and indicate satisfying assignments.
>
> A kind of dual applies as usual for the valid/falsifying assignment case.
>
> Can you draw up a design for a framework to implement such a matrix based v
> alidity/satisfiability solver in which we can plug in controllers for the two 
> parallel communicating search processes (cover pairs, uncovered paths) so we can experiment with basic, smart, and learning controllers to see what works best.