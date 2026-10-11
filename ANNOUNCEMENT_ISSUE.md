@openai — [openai/math](https://github.com/openai/math)

**OpenAI needed a 66×66 matrix to break polynomial removal. We did it with 4×4.**

我看oai也就那么回事。🖕🏻

I have released the complete Lean 4 source package for **A Four-by-Four Obstruction to Polynomial Removal for Ordered Binary Matrices**.

The manuscript gives a fixed $4\times4$ obstruction, improving the $66\times66$ pattern described in your *Polynomial removal fails for ordered binary matrices*. For $m=2^h$, the host has order $(14h+2)m$, exact unrestricted editing distance $m^2$, and exactly $2m^6+\frac{m-2}{2}m^5$ induced copies. Its original-copy transversal number is exactly $m$.

The release includes all retained certificate modules, pinned dependencies, reproduction scripts, and build and axiom-audit records. The supplied build reports record fresh compilation of all 550 primary project modules. To reproduce, run `bash verify_all.sh` from `formal_verification/` with Lean 4.24.0.

The manuscript credits your tree-propagation construction and identifies the smaller forcing frame and exact classifications as its quantitative contributions. I would welcome a technical review of the all-depth classification, canonical repair, and arbitrary-edit lower bound.

Read the [21-page manuscript (PDF)](https://github.com/wzn1118/h4-ordered-matrix-removal/blob/main/paper.pdf) and [complete Lean 4 formalization](https://github.com/wzn1118/h4-ordered-matrix-removal/tree/main/formal_verification).
