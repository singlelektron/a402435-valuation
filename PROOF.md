# The exact 2-adic valuation in A402435

Let $T(r,k)$ denote the entries of Kurkov's weighted Entringer triangle A386363, and write $D(n)=T(n,n)$. Let $s_2(n)$ denote the sum of the binary digits of $n$ and $v_2$ the 2-adic valuation. We prove that for every $n\ge1$, the diagonal satisfies $v_2(D(n))+f(n)=n+1$, where $f$ is Luschny's correction term in A402435. The initial entry is $T(0,0)=1$. For $r\ge1$, set $T(r,0)=0$ and $T(r,1)=D(r-1)$. For $2\le k\le r$, set $T(r,k)=T(r,k-1)+(r-2)T(r-1,r-k)$. All entries are nonnegative. In each row of positive index, column 1 contains the previous diagonal entry and subsequent entries are nondecreasing. Since $D(0)=1$, induction gives $D(n)>0$, so the valuation of $D(n)$ is defined throughout. [Triangle definition and theorem](MathMiner/Problems/A402435/Statement.lean) · [Positivity of the diagonal](MathMiner/Problems/A402435/RowBounds.lean) · [OEIS conjecture](https://oeis.org/A402435/internal)

## From the triangle to a differential equation

Set $F_r(k)=T(r+2,k+1)$ and write $\Delta F(k)=F(k+1)-F(k)$ for the forward difference. The last step adds a multiple of the entry in column zero, which vanishes. Hence for every $r\ge0$ we have $F_r(r)=D(r+2)$. On the range $0\le k\le r$, taking two differences in the row recurrence gives

$$
\Delta^2 F_{r+2}(k)=-(r+2)(r+1)F_r(k).
$$

At the left endpoint, $F_r(0)=D(r+1)$, and for $r\ge1$ we have $\Delta F_r(0)=rD(r+1)$. Each application of the second-difference identity lowers the row index by two, giving

$$
\Delta^j F_r(0)=(-1)^{\lfloor j/2\rfloor}r^{\underline j}
D\bigl(r+1-2\lfloor j/2\rfloor\bigr),\qquad 0\le j\le r.
$$

Here $r^{\underline j}=r!/(r-j)!$. Evaluating Newton's forward formula at $k=r$ and using $r^{\underline j}=j!\binom rj$ gives

$$
D(r+2)=\sum_{j=0}^r (-1)^{\lfloor j/2\rfloor}
\binom rj^2 j!\,D\bigl(r+1-2\lfloor j/2\rfloor\bigr).
$$

The expansion starts at column $1$ and ends at column $r+1$. The last column has the same value as this endpoint, so the expansion reaches the diagonal value while keeping each second difference within its valid range. [Second differences within a row](MathMiner/Problems/A402435/Moments.lean) · [Newton recurrence](MathMiner/Problems/A402435/Newton.lean)

In $\mathbb Q[[x]]$, set

$$
y_r=\frac{D(r+1)}{(r!)^2},\qquad Y=\sum_{r\ge0}y_rx^r,\qquad LH=(xH')'.
$$

Then $[x^r]LH=(r+1)^2[x^{r+1}]H$. After division by $(r!)^2$, the term for even $j=2k$ is $(-1)^k y_{r-2k}/(2k)!$, and the term for odd $j=2k+1$ is $(-1)^k(r-2k)^2 y_{r-2k}/(2k+1)!$. Write $C=\cos x$ and $S=\sin x$. Summing the two convolutions gives $(1-S)LY=CY$. Since $C^2+S^2=1$ and $C(0)=1$, we obtain

$$
C LY=(1+S)Y.
$$

In October 2026, ProveIt's *Research report 180* derived this equation and an equivalent coefficient recurrence from the same weighted triangle. On November 20, 2026, Peter Luschny recorded the equivalent equation $(xY')'=(\sec x+\tan x)Y$ and its convolution with squared binomial coefficients in A386381. The formal proof here derives the differential equation from the row recurrence using Newton's forward formula in the ring of formal power series. [Normalized recurrence](MathMiner/Problems/A402435/NormalizedNewton.lean) · [From coefficients to the differential equation](MathMiner/Problems/A402435/SeriesBridge.lean) · [Derivation in the October report](https://github.com/VladimirReshetnikov/ProveIt/blob/3d6e73ab1e4efbbfdb69b6758cade7343f075d01/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a386381-modified-entringer/article.tex#L321-L373) · [Luschny's entry](https://github.com/oeis/oeisdata/blob/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A386/A386381.seq#L14-L16)

## A recurrence for the odd-power coefficients

Write $Y=U+V$, where $U$ contains only even powers and $V$ contains only odd powers. Since $L$ reverses the parity of each degree, comparing the even and odd parts gives

$$
C LV=U+SV,\qquad C LU=V+SU.
$$

Substitute $U=C LV-SV$ into the second equation. Applying the product rule $L(fg)=f Lg+g Lf+2xf'g'$, using $C'=-S$ and $S'=C$, and setting $B=S/C=\tan x$ gives

$$
L^2 V=2xB(LV)' +(x+3B)LV+2xV'+(2-xB)V.
$$

Set $t_i=[x^{2i+1}]B$, $K_j=(j!)^2[x^{2j+1}]V$, and $Q(m)=(4m+3)(2m+1)^2$. The identity $B'=1+B^2$ gives

$$
t_0=1,\qquad (2i+1)t_i=\sum_{a=0}^{i-1} t_a t_{i-1-a}\quad(i\ge1).
$$

Extract the coefficient of $x^{2j+1}$ in the equation for the odd part. In the product of $B$ with $2x(LV)'+3LV$, the coefficient of $x^{2m}$ in the second factor is $Q(m)[x^{2m+1}]V$. The term $-xBV$ contributes $-t_{i-1}[x^{2(j-i)+1}]V$ for $i\ge1$. Combining the $i=0$ term with the terms that have no factor of $B$ and multiplying by $(j!)^2/4$ gives

$$
\begin{split}
(2j+3)^2K_{j+1}&=(j+1)((2j+1)^2+1)K_j+
\sum_{i=1}^j W_{j,i}K_{j-i},\\
W_{j,i}&=\frac{(j^{\underline i})^2}{4}\bigl(Q(j-i)t_i-t_{i-1}\bigr).
\end{split}
$$

Since $D(2)=1$, we have $K_0=1$. [Formal elimination](MathMiner/Problems/A402435/SeriesElimination.lean) · [Coefficient recurrence](MathMiner/Problems/A402435/TangentRecurrence.lean)

## Odd denominators and the certificate modulo 16

Let $R=\mathbb Z_{(2)}$ be the ring of rational numbers that can be written with an odd denominator. The reduction map $R\to\mathbb Z/16\mathbb Z$ sends a fraction to its numerator times the multiplicative inverse of its denominator. Each $t_i$ lies in $R$ because its recurrence divides only by the odd number $2i+1$. The first four coefficients are $1,1/3,2/15,17/315$. Setting $m=j-i$ and substituting gives the following weights.

| $i$ | $W_{j,i}$ |
|---|---|
| $1$ | $j^2m(4m^2+7m+4)/3$ |
| $2$ | $\binom j2^2(2Q(m)-5)/15$ |
| $3$ | $\binom j3^2(17Q(m)-42)/35$ |

For $4\le i\le j$, the product $j^{\underline i}$ contains at least four consecutive integers and is therefore divisible by $8$. Its square divided by $4$ is still divisible by $16$. Thus every weight $W_{j,i}$ lies in $R$, and for $i\ge4$ the weight belongs to $16R$. In the formula for $W_{j,1}$, the denominator $4$ cancels because $Q(m)-3=4m(4m^2+7m+4)$. Since $(2j+3)^2$ is odd, induction from $K_0=1$ gives $K_j\in R$ for every index, so we can reduce the entire recurrence modulo 16. [Divisibility of the higher-order terms](MathMiner/Problems/A402435/IntegralRecurrence.lean) · [Reduction map](MathMiner/Problems/A402435/Reduction.lean)

Only the four terms involving $K_j,K_{j-1},K_{j-2},K_{j-3}$ remain. Let $e_j$ be the sequence of period 16 given in the table.

| $j\bmod16$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $e_j$ | 1 | 2 | 8 | 7 | 9 | 10 | 12 | 7 | 9 | 2 | 8 | 7 | 9 | 10 | 12 | 15 |

Multiply the four-term recurrence by $105$ to clear the denominators $3,15,35$, then substitute the table entries in $\mathbb Z/16\mathbb Z$. Terms with $i>j$ are taken to be zero. For $j\ge3$, all indices on the right are nonnegative. The shift $j\mapsto j+32$ preserves the polynomial values modulo 16 and the values of $e$. Pascal's recurrence also gives $\binom{j+32}{2}\equiv\binom j2$ and $\binom{j+32}{3}\equiv\binom j3\pmod{16}$. It therefore suffices to check the initial steps $0,1,2$ and one full period $3\le j\le34$. Lean verifies these 35 steps by reduction and uses the shift to extend the check to every index. Since $105(2j+3)^2$ is a unit, the preceding terms uniquely determine the next one. Together with $e_0=K_0=1$, this proves $K_j\equiv e_j\pmod{16}$ for all $j$. [Finite certificate and induction](MathMiner/Problems/A402435/ModularCertificate.lean)

## The valuation at even indices

Using $K_j=(j!)^2y_{2j+1}$ and splitting $(2j+1)!$ into its odd and even factors gives

$$
D(2j+2)=4^j\big((2j+1)!!\big)^2 K_j.
$$

Every entry in the residue table is nonzero modulo 16, so each $e_j$ determines the exact value of $v_2(K_j)$. The following table matches these valuations to the correction term for each even residue class.

| $j\bmod8$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $n=2j+2\bmod16$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 0 |
| $v_2(K_j)$ | 0 | 1 | 3 | 0 | 0 | 1 | 2 | 0 |
| $f(n)$ | 3 | 2 | 0 | 3 | 3 | 2 | 1 | 3 |

Thus $v_2(D(n))+f(n)=2j+v_2(K_j)+f(n)=2j+3=n+1$. The case $j=0$ gives $n=2$, so this covers every positive even index. [Factorial scaling](MathMiner/Problems/A402435/EvenScaling.lean) · [Recovering the valuation from the residue](MathMiner/Problems/A402435/EvenBranch.lean)

## The valuation at odd indices

Return to $U=C LV-SV$ and set $H_m=(2m)![x^{2m}]U=D(2m+1)/(2m)!$. Using $K_j$ to express the coefficients of $V$ and expanding the two products gives

$$
\begin{split}
H_m={}&\sum_{j=0}^m(-1)^{m-j}\binom{2m}{2j}\binom{2j}j(2j+1)^2K_j\\
&-\sum_{j=0}^{m-1}(-1)^{m-j-1}\binom{2m}{2j+1}(2j+1)\binom{2j}jK_j .
\end{split}
$$

The factorial factor comes from $(2j)!/(j!)^2=\binom{2j}j$. The second sum ends at $m-1$ because the lowest degree in both $S$ and $V$ is one. Both sums lie in $R$. Every term with $j>0$ contains the even factor $\binom{2j}j=2\binom{2j-1}{j-1}$. At $j=0$, the term in the second sum contains $\binom{2m}1=2m$, and at $j=0$ the term in the first sum equals $(-1)^mK_0=(-1)^m$. Hence $H_m$ is congruent to 1 modulo 2, including the case $m=0$ when the second sum is empty. [Reconstructing the even-power coefficients](MathMiner/Problems/A402435/OddCoefficients.lean) · [Parity of the normalized coefficient](MathMiner/Problems/A402435/OddUnit.lean)

It follows that $v_2(D(2m+1))=v_2((2m)!)=2m-s_2(2m)$, where the second equality is Legendre's formula. Since $f(2m+1)=1+s_2(2m+1)=2+s_2(2m)$, adding the valuation and the correction term gives $2m+2$. Taking $m=0$ covers $n=1$. Together with the even case, this proves the exact valuation formula for every positive index. [Equivalent formulation at odd indices](MathMiner/Problems/A402435/OddBranch.lean) · [Proof for odd indices](MathMiner/Problems/A402435/OddProof.lean)
