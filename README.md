# A Four-by-Four Obstruction to Polynomial Removal for Ordered Binary Matrices

**Author:** Zinan Wang  
**Research area:** Extremal combinatorics; induced removal for ordered binary matrices

For each integer $h\ge1$, set $m=2^h$. The manuscript constructs an ordered binary matrix $A_h$ of order $(14h+2)m$ for the fixed pattern

$$
H_4=\begin{pmatrix}0&1&1&0\\1&0&0&1\\1&0&1&0\\0&1&1&1\end{pmatrix}.
$$

The asserted exact identities are

$$
D_{H_4}(A_h)=m^2, \qquad N_{H_4}(A_h)=2m^6+\frac{m-2}{2}m^5.
$$

The resulting normalized edit distance is $(14h+2)^{-2}$ and the induced-copy density is $\Theta(4^{-h}h^{-8})$. The manuscript also establishes an original-copy transversal number of $m$.

## Research provenance

The manuscript cites the 2026 work *Polynomial removal fails for ordered binary matrices* in [openai/math](https://github.com/openai/math) and considers a fixed $4\times4$ obstruction with exact copy and edit-distance calculations.

## Source release

**Publication status:** The repository has been initialized; upload of the complete Lean 4 proof project, manuscript source, certificate files, and reproducibility records remains pending. Do not treat this initial README commit as a complete source or verification release.

The intended source package is `H4_GitHub_Complete_Public_Release_2026-10-11.zip` (678 archive entries, including the main Lean 4 formalization and its certificates). The pinned primary Lean toolchain is version 4.24.0.
