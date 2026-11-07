<!-- Adapted from XinyuanXie-hub/Konig-constant, commit 165a31717d8084e6df9a7c8f745059af0e2ed40a, under Apache-2.0. Mathematical statements, source reference, and verification links changed for Szarek. -->
<!-- Original adaptation notice: Adapted from XinyuanXie-hub/cyclic-lsi-new, commit 4b4ff9a506c0aac696119542b76276238c14cb9b, under Apache-2.0. Mathematical statement and verification links changed for König; pictures omitted. -->

# Stability of Szarek's inequality with best constant

This project uses Lean to verify Theorems 1 and 2 of the paper cited below.

> Xinyuan Xie,
> *Stability of Szarek's inequality with best constant*,
> [arXiv:2610.07526](https://arxiv.org/abs/2610.07526).

## Mathematical statements

Let $`\varepsilon_1,\ldots,\varepsilon_n`$ be independent Rademacher random variables, each taking the values $`-1`$ and $`1`$ with equal probability. Throughout, $`\|\cdot\|_2`$ denotes the Euclidean norm, and $`e_1,\ldots,e_n`$ are the standard coordinate vectors.

<a name="theorem-1"></a>

**Theorem 1.** For every $`n\geq2`$ and every unit vector $`a\in\mathbb R^n`$ with $`a_1\geq\cdots\geq a_n\geq0`$,

```math
\mathbb E\left|\sum_{j=1}^{n}a_j\varepsilon_j\right|
\geq \frac{1}{\sqrt{2}}+
\frac{(2-\sqrt{2})^{3/2}}{8}
\left\|a-\frac{e_1+e_2}{\sqrt{2}}\right\|_2.
```

The constant $`(2-\sqrt{2})^{3/2}/8`$ is optimal among constants valid for all such dimensions and vectors. Equality is attained by $`a=\tfrac12(1,1,1,1,0,\ldots,0)`$ for every $`n\geq4`$.

Define Haagerup's function by

```math
F(s):=\frac{2}{\sqrt{\pi s}}
\frac{\Gamma((s+1)/2)}{\Gamma(s/2)},\qquad s>0.
```

<a name="theorem-2"></a>

**Theorem 2.** For every $`n\geq2`$ and every unit vector $`a\in\mathbb R^n`$ with $`a_1\geq\cdots\geq a_n\geq0`$ and $`a_1+a_2\leq1`$,

```math
\mathbb E\left|\sum_{j=1}^{n}a_j\varepsilon_j\right|
\geq F\left(\frac{4}{(a_1+a_2)^2}\right)
\geq \frac34+\frac{1-(a_1+a_2)^2}{24}.
```

The first inequality is attained when the first $`2m`$ coordinates of $`a`$ are equal to $`1/\sqrt{2m}`$ and the remaining coordinates are zero, for every integer $`m\geq2`$ and every $`n\geq2m`$.

## Verification

To verify the correctness of the theorems in Lean, one only needs to check that the statements and definitions in [Challenge.lean](Challenge.lean) match [Theorem 1](#theorem-1) and [Theorem 2](#theorem-2) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the latest “Lean CI” workflow run on `main`, or open it directly from [here](https://xinyuanxie-hub.github.io/Szarek-stability/latest-run/).
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the end of the log reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.

Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.
