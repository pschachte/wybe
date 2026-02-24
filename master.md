# Master Doc for my Thesis

I need to implement "Implement escape analysis and use the results to turn heap allocations into stack allocations",
and also possibly "GC-free automatic memory management".

Looking at the plan from Gemini, it seems like escape analysis is an easy change to implement.

> One thing I noticed is that Gemini mentioned that if we have stack allocations, we can't use tail recursion optimization.
> Implementing tail call optimization for functions with stack allocations could be a follow up task. (Check with professor)

Upon asking Gemini to come up with a plan for improving the alias analysis, it turns out that we might need to completely change the underlying implementation of the alias analysis from a Disjoint Set to a Points To Graph. This seems like a large change. 

## TODOs

- [ ] Check Escape Analysis plan with professor.
- [ ] Check tail call optimization plan with professor.
- [ ] Talk about the alias analysis change with the professor. It seems like a big change.