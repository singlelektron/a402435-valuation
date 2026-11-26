# A402435 的精确二进估值

设 $T(r,k)$ 为 Kurkov 的加权 Entringer 三角形 A386363，$D(n)=T(n,n)$。记 $s_2(n)$ 为 $n$ 的二进制数位和，$v_2$ 为二进估值。我们证明，对每个 $n\ge1$，都有 $v_2(D(n))+f(n)=n+1$，其中 $f$ 是 Luschny 在 A402435 中指定的修正项。初值为 $T(0,0)=1$。对 $r\ge1$，令 $T(r,0)=0$、$T(r,1)=D(r-1)$；对 $2\le k\le r$，令 $T(r,k)=T(r,k-1)+(r-2)T(r-1,r-k)$。各项非负，每一正行的第一列等于上一行的对角项，后续列单调不减。由 $D(0)=1$ 得 $D(n)>0$，下文对 $D(n)$ 取估值均有意义。[三角形与命题的定义](MathMiner/Problems/A402435/Statement.lean) · [对角项正性](MathMiner/Problems/A402435/RowBounds.lean) · [OEIS 猜想](https://oeis.org/A402435/internal)

## 从三角形得到微分方程

令 $F_r(k)=T(r+2,k+1)$，$\Delta F(k)=F(k+1)-F(k)$。因下一步加上的是第零列的倍数，对每个 $r\ge0$ 都有 $F_r(r)=D(r+2)$。在 $0\le k\le r$ 上，对原行递推取两次差分得到

$$
\Delta^2 F_{r+2}(k)=-(r+2)(r+1)F_r(k).
$$

在左端，$F_r(0)=D(r+1)$，且 $r\ge1$ 时 $\Delta F_r(0)=rD(r+1)$。每次消去两阶差分便降低两行，得到

$$
\Delta^j F_r(0)=(-1)^{\lfloor j/2\rfloor}r^{\underline j}
D\bigl(r+1-2\lfloor j/2\rfloor\bigr),\qquad 0\le j\le r.
$$

这里 $r^{\underline j}=r!/(r-j)!$。在 $k=r$ 代入 Newton 前进公式，并用 $r^{\underline j}=j!\binom rj$，得到

$$
D(r+2)=\sum_{j=0}^r (-1)^{\lfloor j/2\rfloor}
\binom rj^2 j!\,D\bigl(r+1-2\lfloor j/2\rfloor\bigr).
$$

展开点是列 $1$，终点是列 $r+1$。最后一列与终点等值，这保证每一次二阶差分都在有效区间内。[行内二阶差分](MathMiner/Problems/A402435/Moments.lean) · [Newton 递推](MathMiner/Problems/A402435/Newton.lean)

在 $\mathbb Q[[x]]$ 中令

$$
y_r=\frac{D(r+1)}{(r!)^2},\qquad Y=\sum_{r\ge0}y_rx^r,\qquad LH=(xH')'.
$$

于是 $[x^r]LH=(r+1)^2[x^{r+1}]H$。上述递推除以 $(r!)^2$ 后，偶数 $j=2k$ 的项为 $(-1)^k y_{r-2k}/(2k)!$，奇数 $j=2k+1$ 的项为 $(-1)^k(r-2k)^2 y_{r-2k}/(2k+1)!$。记 $C=\cos x$，$S=\sin x$，将两种卷积分别求和，即有 $(1-S)LY=CY$。由 $C^2+S^2=1$ 和 $C(0)=1$ 可得

$$
C LY=(1+S)Y.
$$

ProveIt 的《Research report 180》于 2026 年 10 月已从同一加权三角形导出该方程及等价的系数递推。Peter Luschny 于 2026-11-20 在 A386381 中列出了等价方程 $(xY')'=(\sec x+\tan x)Y$ 及其二项式平方卷积。这里用 Newton 前进公式从行递推形式化推导该微分方程，全程在形式幂级数环中运算。[归一化递推](MathMiner/Problems/A402435/NormalizedNewton.lean) · [系数与微分方程](MathMiner/Problems/A402435/SeriesBridge.lean) · [十月报告的推导](https://github.com/VladimirReshetnikov/ProveIt/blob/3d6e73ab1e4efbbfdb69b6758cade7343f075d01/SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a386381-modified-entringer/article.tex#L321-L373) · [Luschny 的原始记录](https://github.com/oeis/oeisdata/blob/976b0c73e00453b1c1e6f16d83108cb9bb744c3b/seq/A386/A386381.seq#L14-L16)

## 奇次幂系数的递推

分解 $Y=U+V$，其中 $U$ 只含偶次幂，$V$ 只含奇次幂。$L$ 交换次数的奇偶性，故比较方程两边得到

$$
C LV=U+SV,\qquad C LU=V+SU.
$$

将 $U=C LV-SV$ 代入第二式。用 $L(fg)=f Lg+g Lf+2xf'g'$、$C'=-S$、$S'=C$ 化简，令 $B=S/C=\tan x$，则

$$
L^2 V=2xB(LV)' +(x+3B)LV+2xV'+(2-xB)V.
$$

令 $t_i=[x^{2i+1}]B$，$K_j=(j!)^2[x^{2j+1}]V$，$Q(m)=(4m+3)(2m+1)^2$。由 $B'=1+B^2$ 得

$$
t_0=1,\qquad (2i+1)t_i=\sum_{a=0}^{i-1} t_a t_{i-1-a}\quad(i\ge1).
$$

在消元方程中取 $x^{2j+1}$ 的系数。$B$ 乘以 $2x(LV)'+3LV$ 时，后者的 $x^{2m}$ 系数是 $Q(m)[x^{2m+1}]V$；而 $-xBV$ 给出 $-t_{i-1}[x^{2(j-i)+1}]V$（$i\ge1$）。把 $i=0$ 的项与未乘 $B$ 的项合并，再乘以 $(j!)^2/4$，得到

$$
\begin{split}
(2j+3)^2K_{j+1}&=(j+1)((2j+1)^2+1)K_j+
\sum_{i=1}^j W_{j,i}K_{j-i},\\
W_{j,i}&=\frac{(j^{\underline i})^2}{4}\bigl(Q(j-i)t_i-t_{i-1}\bigr).
\end{split}
$$

由 $D(2)=1$ 可知 $K_0=1$。[形式消元](MathMiner/Problems/A402435/SeriesElimination.lean) · [系数递推](MathMiner/Problems/A402435/TangentRecurrence.lean)

## 奇分母与模 16 证书

设 $R=\mathbb Z_{(2)}$ 为所有可以写成奇分母分数的有理数。约化 $R\to\mathbb Z/16\mathbb Z$ 时将分母取乘法逆元。每个 $t_i$ 都在 $R$ 中，因为其递推仅除以奇数 $2i+1$。前四项为 $1,1/3,2/15,17/315$。设 $m=j-i$，代入得到

| $i$ | $W_{j,i}$ |
|---|---|
| $1$ | $j^2m(4m^2+7m+4)/3$ |
| $2$ | $\binom j2^2(2Q(m)-5)/15$ |
| $3$ | $\binom j3^2(17Q(m)-42)/35$ |

对于 $4\le i\le j$，$j^{\underline i}$ 至少含四个连续整数，故可被 $8$ 整除，其平方除以 $4$ 后仍可被 $16$ 整除。因此所有 $W_{j,i}$ 在 $R$ 中，$i\ge4$ 时属于 $16R$。注意 $W_{j,1}$ 的分母 $4$ 是由 $Q(m)-3=4m(4m^2+7m+4)$ 消去的。因 $(2j+3)^2$ 是奇数，从 $K_0=1$ 归纳，得到所有 $K_j\in R$，可以对整条递推取模。[切去高阶项的整除证明](MathMiner/Problems/A402435/IntegralRecurrence.lean) · [约化映射](MathMiner/Problems/A402435/Reduction.lean)

递推只剩 $K_j,K_{j-1},K_{j-2},K_{j-3}$ 四项。令 $e_j$ 为下表的 16 周期序列。

| $j\bmod16$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| $e_j$ | 1 | 2 | 8 | 7 | 9 | 10 | 12 | 7 | 9 | 2 | 8 | 7 | 9 | 10 | 12 | 15 |

表的验证方法如下。将四项递推乘以 $105$，清除分母 $3,15,35$，便可在 $\mathbb Z/16\mathbb Z$ 中逐项代入。$i>j$ 的项取零。在 $j\ge3$ 时，所有回看的下标都非负；平移 $j\mapsto j+32$ 后，各多项式和 $e$ 值不变。由 Pascal 递推也有 $\binom{j+32}{2}\equiv\binom j2$、$\binom{j+32}{3}\equiv\binom j3\pmod{16}$。所以只须检查 $0,1,2$ 三个起始步骤及 $3\le j\le34$ 的一整周期。Lean 对这 35 个步骤逐项归约，再用平移证明表满足每一步递推。因 $105(2j+3)^2$ 是单位，下一项由前项唯一确定，且 $e_0=K_0=1$，从而 $K_j\equiv e_j\pmod{16}$ 对所有 $j$ 成立。[有限证书及归纳](MathMiner/Problems/A402435/ModularCertificate.lean)

## 回到偶数下标

由 $K_j=(j!)^2y_{2j+1}$，把 $(2j+1)!$ 拆成奇数与偶数的乘积，得

$$
D(2j+2)=4^j\big((2j+1)!!\big)^2 K_j.
$$

上表各项均非零模 16，所以每个 $e_j$ 都能确定 $v_2(K_j)$ 的精确值。下表把它与原题的偶数分支逐类对齐。

| $j\bmod8$ | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| $n=2j+2\bmod16$ | 2 | 4 | 6 | 8 | 10 | 12 | 14 | 0 |
| $v_2(K_j)$ | 0 | 1 | 3 | 0 | 0 | 1 | 2 | 0 |
| $f(n)$ | 3 | 2 | 0 | 3 | 3 | 2 | 1 | 3 |

因此 $v_2(D(n))+f(n)=2j+v_2(K_j)+f(n)=2j+3=n+1$。$j=0$ 对应 $n=2$，所有正偶数都被覆盖。[阶乘缩放](MathMiner/Problems/A402435/EvenScaling.lean) · [从余数恢复估值](MathMiner/Problems/A402435/EvenBranch.lean)

## 回到奇数下标

再次使用 $U=C LV-SV$。设 $H_m=(2m)![x^{2m}]U=D(2m+1)/(2m)!$。以 $K_j$ 表示 $V$ 的系数，分别展开两个乘积，得

$$
\begin{split}
H_m={}&\sum_{j=0}^m(-1)^{m-j}\binom{2m}{2j}\binom{2j}j(2j+1)^2K_j\\
&-\sum_{j=0}^{m-1}(-1)^{m-j-1}\binom{2m}{2j+1}(2j+1)\binom{2j}jK_j .
\end{split}
$$

阶乘因子来自 $(2j)!/(j!)^2=\binom{2j}j$；第二个和上限为 $m-1$，因为 $S$ 和 $V$ 的最低次都是一次。两和均在 $R$ 中。所有 $j>0$ 的项均含偶数 $\binom{2j}j=2\binom{2j-1}{j-1}$。第二个和在 $j=0$ 时含 $\binom{2m}1=2m$，第一个和在 $j=0$ 时为 $(-1)^mK_0=(-1)^m$。于是 $H_m$ 模 2 等于 1，包括第二个和为空的 $m=0$。[偶次幂的重构](MathMiner/Problems/A402435/OddCoefficients.lean) · [奇性](MathMiner/Problems/A402435/OddUnit.lean)

因此 $v_2(D(2m+1))=v_2((2m)!)=2m-s_2(2m)$，第二个等号是 Legendre 公式。又 $f(2m+1)=1+s_2(2m+1)=2+s_2(2m)$，两式相加为 $2m+2$。取 $m=0$ 包含 $n=1$。这与偶数支合起来证明了所有正整数下标的精确估值公式。[奇数支的等价形式](MathMiner/Problems/A402435/OddBranch.lean) · [奇数支证明](MathMiner/Problems/A402435/OddProof.lean)
