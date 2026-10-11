# A Four-by-Four Obstruction to Polynomial Removal for Ordered Binary Matrices

This manuscript presents a fixed \(4\times4\) ordered binary pattern for which polynomial induced removal bounds fail, together with exact counting identities, unrestricted editing-distance bounds, and a Lean 4 verification package.

**[Read the 21-page paper (PDF)](paper.pdf)** · [LaTeX source](paper/main.tex) · [Lean 4 formalization](formal_verification/)

Complete Lean 4 source release accompanying the manuscript by Zinan Wang.

## Results

For every integer $h\ge 1$, let $m=2^h$. The manuscript constructs a binary matrix $A_h$ of order $(14h+2)m$ for the fixed pattern

$$H_4=\begin{pmatrix}0&1&1&0\\1&0&0&1\\1&0&1&0\\0&1&1&1\end{pmatrix}.$$

Its stated exact identities are

$$D_{H_4}(A_h)=m^2,\qquad N_{H_4}(A_h)=2m^6+\frac{m-2}{2}m^5.$$

The normalized editing distance is $(14h+2)^{-2}$ and the induced-copy density is $\Theta(4^{-h}h^{-8})$. Consequently this fixed pattern admits no polynomial induced ordered removal bound. The original-copy transversal number is exactly $m$.

## Relation to prior work

The manuscript cites OpenAI's *Polynomial removal fails for ordered binary matrices*, dated September 25, 2026, in [openai/math](https://github.com/openai/math). It describes the earlier obstruction as a $66\times66$ pattern and gives a $4\times4$ obstruction, together with exact counting, unrestricted editing distance, and the original-copy transversal number. This is the specific quantitative improvement documented by this release. The construction uses the tree-propagation approach credited to that prior work.

## Reproduce

The complete original ancillary release is present in `formal_verification/`. All 664 retained files are preserved byte-for-byte from the supplied release. `RELEASE_SHA256.json` provides their hashes.

Install Lean 4.24.0 through elan, then run:

```sh
cd formal_verification
bash verify_all.sh
```

The pinned dependencies are recorded in `lake-manifest.json`. The script builds the primary project and the included supplemental projects. Network access is needed to obtain dependencies.

## Verification records

`formal_verification/evidence/strict_build/strict_build_run.json` and its continuation report record successful fresh compilation of all 550 primary project modules. The final source-freshness report and axiom-audit records are included. These are retained records from the supplied release; run the commands above for a new local verification.

## Manuscript

[`paper.pdf`](paper.pdf) is the 21-page compiled manuscript built directly from the unmodified [`paper/main.tex`](paper/main.tex) with pdfLaTeX. To rebuild, run `latexmk -pdf main.tex` in `paper/`. The source currently identifies Zinan Wang as its author. arXiv submission metadata also names Xinhao Yang; the manuscript author line should be synchronized with the authors' agreed attribution before resubmission.

## Release contents

- Complete primary Lean project and certificate modules
- Isolated extension core and exact-transversal supplement
- Pinned dependency manifests and reproduction scripts
- Historical build, source-freshness, and axiom-audit records
- Manuscript sources and a proposed GitHub issue announcement
