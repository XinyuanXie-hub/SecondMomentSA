# SecondMomentSA

This project uses Lean to verify Theorem 3.4 (Convergence of practical algorithms) from the following paper:

> Tao Jiang and Lin Xiao, *Second-Moment Stochastic Approximation Methods*, [arXiv:2609.36600v1](https://arxiv.org/html/2609.36600v1).

## Mathematical statements

Let $G(X,\xi)$ be a random matrix-valued regression function. Its first moment is
$M(X)=\mathbf{E}_{\xi}[G(X,\xi)]$. Write $W(X)$ for the second moment, using the
entrywise product, $G(X,\xi)G(X,\xi)^T$, or $G(X,\xi)^T G(X,\xi)$ inside
the expectation as in (4a)–(4c). Write $M_t=M(X_t)$ and $W_t=W(X_t)$, and
let $\hat M_t$ and $\hat W_t$ be the corresponding estimators.
The blending map $\phi$ combines the moments into an update direction.

For weight decay $\lambda\geq 0$, the practical update (49) is

```math
X_{t+1}=(1-\alpha_t\lambda)X_t-\alpha_t\phi(\hat M_t,\hat W_t).
```

The filtration in (50) is
$\mathcal F_t=\sigma(X_0,\xi_0,X_1,\ldots,\xi_{t-1},X_t)$.
The iterates $X_t$ are $\mathcal F_t$-measurable, and the practical direction
$\phi(\hat M_t,\hat W_t)$ is $\mathcal F_{t+1}$-measurable.
Write $\mathbf{E}_t[Z]=\mathbf{E}[Z\mid\mathcal F_t]$. The conditional
variance (51) and practical update deviation (52) are

```math
\begin{aligned}
\mathrm{Var}_t[Z]&=\mathbf{E}_t\bigl[\lVert Z-\mathbf{E}_t[Z]\rVert_F^2\bigr],\\
\epsilon_t&=\bigl\lVert
\mathbf{E}_t[\phi(\hat M_t,\hat W_t)]-\phi(M_t,W_t)
\bigr\rVert_F.
\end{aligned}
```

**Assumption A (Aiming and growth conditions).** There are
$X_*\in\mathbf{R}^{m\times n}$, $\mu>0$, and $L,C\geq 0$ for which every
$X\in\mathbf{R}^{m\times n}$ satisfies (37) and (38).

```math
\begin{aligned}
\bigl\langle\phi(M(X),W(X))+\lambda X, X-X_*\bigr\rangle
&\geq \mu\lVert X-X_*\rVert_F^2,\\
\lVert\phi(M(X),W(X))\rVert_F
&\leq L\lVert X-X_*\rVert_F+C.
\end{aligned}
```

**Assumption B (Practical update deviation bound).** For some constant
$\bar\epsilon\geq 0$, almost surely

```math
\limsup_{t\to\infty}\epsilon_t\leq\bar\epsilon.
```

<a name="theorem-3-4"></a>

**Theorem 3.4.** (Convergence of practical algorithms.) Assume A and B, and suppose that
$\mathbf{E}[\lVert X_0\rVert_F^2]<\infty$. Assume also the following conditions.

1. (a) For some constant $b$, the conditional variance of the practical
   direction satisfies, for every $t\geq 0$, almost surely

   ```math
   \mathrm{Var}_t[\phi(\hat M_t,\hat W_t)]\leq b.
   ```

2. (b) The step sizes $\alpha_t$ are deterministic and satisfy

   ```math
   \alpha_t\geq 0,\qquad
   \sum_{t=0}^{\infty}\alpha_t=\infty,\qquad
   \sum_{t=0}^{\infty}\alpha_t^2<\infty.
   ```

Then the iterates of (49) satisfy the bound (54) almost surely.

```math
\limsup_{t\to\infty}\lVert X_t-X_*\rVert_F\leq\frac{\bar\epsilon}{\mu}.
```

## Verification

To verify the correctness of the theorem in Lean, one only needs to check that the statement and definitions in [Challenge.lean](Challenge.lean) match [Theorem 3.4](#theorem-3-4) stated above, and confirm that `lake comparator` succeeds.

The results of `lake comparator` can be checked through the GitHub workflow provided by this project as follows:

1. Sign in to GitHub, open the “Actions” tab, then open the first workflow run listed there.
2. Click “Verify the Challenge against Solution”, then expand “Run Comparator with Lean, NanoDa, and con-ron”.
3. Check that the log (lines 198–203) reports acceptance by con-ron, NanoDa, and Lean, followed by `Your solution is okay!`.


Note: Here, we use the [“gold standard”](https://lean-lang.org/doc/reference/latest/ValidatingProofs/#validating-comparator) for validating proofs in Lean, and we refer readers to [“Challenges and External Checkers”](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/#lake-comparator) for details on how it works.
