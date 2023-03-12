# Derived Categories in Lean 3

An attempt at formalising derived categories in Lean 3.
The (optimistic) goal is to formalise Beilinson's semi-orthogonal
decomposition for projective space, which roughly says that 
the derived category of projective n-space admits a full 
exceptional sequence given by the line bundles in degrees 0 to n. 

Progress so far:
- Implemented localizing a category at a left multiplicative system. (Reference: Stacks Project Tag 04VB)

Next task:
- Define a derived category as a certain localization of the homotopy category.