# Elementary-Euclidean-Geometry
### Project Title: Formalizing Elementary Euclidean Geometry And The Path to Desargues' Theorem

1. Defining geometric objects (e.g. points, lines, angles, etc.) and formalizing Euclid's postulates in Lean4 [Ref: Euclid.lean (written in Lean3)]
2. Using the axioms and postulates to prove some theorems encountered in high school geometry. [Ref: NCERT Mathematics Class 9, 10]
3. Tentative topics: theorems on angles, transversal & parallel lines, angle sum property of triangles, congruence of triangles.
4. Shift: We shifted to trying to prove Desargues' theorem. For that, we defined the necessary elements of incidence geometry and their properties. But we only managed to reach upto Dilatations and some of their properties.


We are going to proceed in the same order as it is usually presented in the high school textbooks - building up to more complex theorems from basic theorems.


UPDATE: Final Submission for PnP2023 project.

Follow-up:
1. Define Inverse of non-trivial dilatations. Also, there are too many structures. Clean the structure defs
2. Clean-up definitions of length of line segments, measure of angles
3. When you put two lines of the same length on top of each other, do the endpoints coincide for different lp-norms?
Does the field have to be reals or can we just work with lines and circles having rational points on them? 
Meaning: every line of length l, is a copy of $$l \cap \mathbb{Q}$$. Same for circles of radius r.
Thereby, discuss about defining this translation and rotation. Coincidicence for lp-norms can be proved for p > 1 using norm equivalence.
Mathematically $$l \cap \mathbb{Q}$$ allows us flexibility with a cauchy sequence like extension (as R is just closure of Q with the Lp metric p > 1) however need to check if Lean's analysis tools allow for something like that.

4. Would the definition in point 3. help with the "Proof with Diagrams" in Lean?
