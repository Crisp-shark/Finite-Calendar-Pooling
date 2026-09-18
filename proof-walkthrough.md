# Proposition 1：逐步读懂完整证明

本文接着 [README 中的符号和命题说明](README.md)，按《Finite Calendar Pooling: A self-contained recursive proof》（2026-09-17）中 Proposition 1 的 Step 1–5，逐步解释原证明。目标是能向老师说明：**每一步为什么需要、公式如何得到、归纳假设到底在哪里用上。**

> **整条证明主线：**先把“只观察 $s-1$ 个日期时可以隐藏位置”的旧日历 $X$，变成新日历的间隔尺度；再把任意一份 $s$ 日期观察记录近似成只依赖旧日历中 $s-1$ 个位置的记录。最后调用归纳假设。

这里 $\operatorname{Unif}[N]$ 表示在整数 $\{1,\ldots,N\}$ 上均匀分布，$\operatorname{Law}(Y)$ 表示随机变量 $Y$ 的分布。下文仍把两个随机变量的分布距离简写为 $d_{\mathrm{TV}}(Y,Z)$。

## 0. 先弄清归纳的对象

证明对**观察到的日期个数 $s$**归纳。更准确地说，归纳命题是：

> 对每个 $m\geq s$ 和每个 $0<\delta<1$，都能构造一份有有限上界的 $m$ 日期随机日历，使任意两个 $s$ 元位置集对应的观察分布相距至多 $\delta$。

这里要同时覆盖所有 $m\geq s$。因为在从 $s-1$ 走到 $s$ 时，我们要调用旧命题来构造 **$m-1$ 个**旧日期 $X_1,\ldots,X_{m-1}$。既然 $m\geq s$，就有 $m-1\geq s-1$，旧命题正好适用。

边界情形 $s=m$ 时，只有一种位置集 $I=[m]$，所以要比较的分布其实只有一个，结论显然成立。原文仍采用统一的递归构造，以便同时处理全部 $m\geq s$。

归纳步把目标误差 $\varepsilon$ 分成三份：旧日历的误差至多 $\varepsilon/3$；把第一种新观察记录换成理想记录，误差至多 $\varepsilon/3$；把第二种记录做同样替换，再付出至多 $\varepsilon/3$。

## Step 1：只观察一个日期时，为什么宽随机起点就够了？

当 $s=1$，取

$$
H_0=\max\left\{1,\left\lceil\frac{m-1}{\varepsilon}\right\rceil\right\},
\qquad U\sim\operatorname{Unif}[H_0],
\qquad D_j=U+j-1.
$$

每次生成的日历都是

$$
(U,U+1,\ldots,U+m-1),
$$

所以它严格递增，而且 $D_m\leq H_0+m-1$。这给出一个**有限**的上界。

关键是估计 $D_i$ 与 $D_j$ 的分布距离。若 $V\sim\operatorname{Unif}[N]$，把它平移非负整数 $a$ 后，原来的支持集是 $\{1,\ldots,N\}$，新的支持集是 $\{1+a,\ldots,N+a\}$。它们重合的点数为 $\max\{N-a,0\}$，所以

$$
d_{\mathrm{TV}}(V+a,V)
=1-\frac{\max\{N-a,0\}}{N}
=\min\left\{\frac aN,1\right\}.
$$

$D_i$ 和 $D_j$ 就是同一个均匀分布相差 $|i-j|$ 的两个平移。因此

$$
d_{\mathrm{TV}}(D_i,D_j)
=\min\left\{\frac{|i-j|}{H_0},1\right\}
\leq\frac{m-1}{H_0}
\leq\varepsilon.
$$

若 $m=1$，公式中的 $\max\{1,\cdot\}$ 确保 $H_0=1$；此时也只有一个位置，比较条件自动成立。

**小例子。** 令 $m=3$、$\varepsilon=1/4$。此时 $H_0=\lceil2/(1/4)\rceil=8$。若 $U$ 在 $1,\ldots,8$ 上均匀分布，就有 $D=(U,U+1,U+2)$。最远的两个位置 $D_1,D_3$ 的分布只相差两个单位，故距离为 $2/8=1/4$；其余位置对的距离更小。

**这一环的作用：**建立归纳起点。只看一个日期时，随机起点的范围远大于位置造成的平移，就足以隐藏位置。

## Step 2：怎样从旧日历造出新日历？

现在假设 $s\geq2$，并已证明“观察 $s-1$ 个日期”的情形。把旧命题用于 $m-1$ 个位置和误差 $\varepsilon/3$，得到

$$
1\leq X_1<\cdots<X_{m-1}\leq\ell,
\qquad
d_{\mathrm{TV}}(X_E,X_F)\leq\frac{\varepsilon}{3}
$$

对所有 $E,F\in\binom{[m-1]}{s-1}$ 成立。$X$ 是**旧日历**，$\ell$ 是它的有限上界。注意旧日历有 $m-1$ 个日期，因为我们准备构造的新日历有 $m$ 个日期，恰好需要 $m-1$ 个相邻间隔。

定义三个参数：

$$
q=1+\left\lceil\frac{6(s-1)}{\varepsilon}\right\rceil,
\qquad
S=(m-1)q^\ell,
\qquad
H=\left\lceil\frac{6S}{\varepsilon}\right\rceil.
$$

| 参数 | 在构造中的角色 | 后面要控制的误差 |
| --- | --- | --- |
| $q$ | 把旧日期 $X_e$ 变成快速增长的间隔尺度 $q^{X_e}$ | 一段间隔之和与最后一个间隔的距离 |
| $S$ | 所有新间隔之和的确定性上界 | 第一个被观察日期之前最多累积多少间隔 |
| $H$ | 新随机起点 $U$ 的取值范围 | 把此前累积的间隔藏在宽随机起点中 |

**注意是指数 $q^{X_e}$，不是乘积 $qX_e$。** 给定整个旧日历 $X$ 后，独立抽取新间隔

$$
G_e\mid X\sim\operatorname{Unif}[q^{X_e}],
\qquad 1\leq e<m.
$$

再独立抽取 $U\sim\operatorname{Unif}[H]$，定义

$$
D_j=U+\sum_{e<j}G_e.
$$

也就是说

$$
D_1=U,\quad D_2=U+G_1,\quad
D_3=U+G_1+G_2,\quad\ldots
$$

每个 $G_e\geq1$，所以每次生成都满足 $D_1<\cdots<D_m$。又因为 $X_e\leq\ell$，所以 $G_e\leq q^\ell$，进而

$$
\sum_{e=1}^{m-1}G_e\leq(m-1)q^\ell=S,
\qquad
D_m\leq H+S.
$$

于是新日历也有一个有限上界 $L=H+S$。**到这里证明的是“构造合法”；接下来才证明它能隐藏观察位置。**

## Step 3：为什么一整段间隔之和近似于最后一个间隔？

固定旧日历的一次可能取值 $X=x$，并取 $1\leq a\leq b<m$。把一段间隔写成

$$
\sum_{e=a}^{b}G_e
=G_b+W_{a,b},
\qquad
W_{a,b}:=\sum_{e=a}^{b-1}G_e.
$$

给定完整的 $X=x$ 以后，$G_a,\ldots,G_b$ 相互独立，因此 $W_{a,b}$ 与 $G_b$ 独立。$G_b$ 均匀分布在 $1,\ldots,q^{x_b}$ 上。

Step 1 的均匀平移公式也适用于**随机平移**：若 $V\sim\operatorname{Unif}[N]$，$W$ 是与 $V$ 独立的非负整数随机变量，那么先固定 $W=w$ 再平均，可得

$$
d_{\mathrm{TV}}(V+W,V)
\leq\mathbb E\min\left\{\frac WN,1\right\}
\leq\frac{\mathbb EW}{N}.
$$

这里第一个“不等于而是小于等于”的原因是：对不同 $w$ 的条件分布做混合时，全变差距离不会超过各条件距离的加权平均。

将 $V=G_b$、$W=W_{a,b}$、$N=q^{x_b}$ 代入。对 $e<b$，

$$
\mathbb E(G_e\mid X=x)
=\frac{q^{x_e}+1}{2}
\leq q^{x_e}.
$$

因此

$$
\begin{aligned}
d_{\mathrm{TV}}\!\left(
\operatorname{Law}\left(\sum_{e=a}^{b}G_e\mid X=x\right),
\operatorname{Law}(G_b\mid X=x)
\right)
&\leq \frac{\sum_{e=a}^{b-1}\mathbb E(G_e\mid X=x)}{q^{x_b}}\\
&\leq \sum_{e=a}^{b-1}q^{x_e-x_b}.
\end{aligned}
$$

**最关键的一跳在这里：**$x_1<\cdots<x_{m-1}$ 是严格递增的整数，所以相邻指数至少差 $1$。从 $e$ 走到 $b$ 一共走 $b-e$ 步，于是 $x_b-x_e\geq b-e$。因此

$$
\sum_{e=a}^{b-1}q^{x_e-x_b}
\leq\sum_{e=a}^{b-1}q^{-(b-e)}
\leq\sum_{t=1}^{\infty}q^{-t}
=\frac1{q-1}.
$$

这正是原文的式 (5)。**并不需要额外假设旧日期之间隔得很远**；只要它们是严格递增的整数，指数形式就自动使前面间隔的影响按几何级数衰减。若 $a=b$，这段本来就只有 $G_b$，替换误差是 $0$。

**数值直觉。** 假设某次固定的旧指数为 $x=(1,2,3)$，并暂取 $q=10$。比较 $G_1+G_2+G_3$ 与 $G_3$：前两段的长度上界为 $10,100$，最后一段的长度是 $1000$。上式给出距离至多

$$
\frac{10+100}{1000}=0.11
\leq\frac1{10-1}.
$$

这只是演示 Step 3 的**条件估计**；正式构造中的 $q$ 按 Step 2 的公式选择。

还需要一个相似的估计。第 $i$ 个位置之前的前缀间隔

$$
P_i:=\sum_{e<i}G_e
$$

总有 $0\leq P_i\leq S$。$U$ 与这些间隔独立，所以同一个均匀平移界给出

$$
d_{\mathrm{TV}}(U+P_i,U\mid X=x)
\leq\frac{\mathbb E(P_i\mid X=x)}H
\leq\frac SH.
$$

**这一环的作用：**后面可以把观察记录中的“整段间隔之和”换成“该段最后一个间隔”，并把第一个日期前的前缀和从 $U$ 中去掉。

## Step 4：为什么要把日期改写成“首日 + 相邻差”？

固定一组被观察的位置

$$
I=\{i_1<\cdots<i_s\}.
$$

原本观察到的是 $D_I=(D_{i_1},\ldots,D_{i_s})$。改写为

$$
Y_I=
\bigl(D_{i_1},\,D_{i_2}-D_{i_1},\,\ldots,\,D_{i_s}-D_{i_{s-1}}\bigr).
$$

这是**可逆**的：若知道首日 $y_1$ 和后续差 $y_2,\ldots,y_s$，就能依次恢复原日期

$$
d_{i_1}=y_1,\qquad
d_{i_t}=y_1+y_2+\cdots+y_t\quad(2\leq t\leq s).
$$

可逆变换只是把可能结果重新标号，因此不改变全变差距离。这样做的好处是，每个相邻差刚好是一段**互不重叠**的 $G_e$ 之和：

$$
Y_I=
\left(
U+\sum_{e<i_1}G_e,\quad
\left(\sum_{e=i_t}^{i_{t+1}-1}G_e\right)_{t=1}^{s-1}
\right).
$$

用 Step 3 的估计，把首项换成 $U$，并把每段间隔之和换成该段最后一个间隔，得到辅助记录

$$
\widetilde Y_I
=(U,G_{i_2-1},G_{i_3-1},\ldots,G_{i_s-1}).
$$

为什么可以把**各坐标**的误差相加？必须先固定完整的 $X=x$。给定 $X=x$ 后，$Y_I$ 的首项使用 $U$ 和位置 $i_1$ 之前的间隔，后续各项使用互不重叠的间隔块，所以各坐标独立。$\widetilde Y_I$ 的坐标在相同条件下也独立。对两个乘积分布，逐个替换坐标并用三角不等式，就有“整个向量的全变差距离不超过各坐标距离之和”。

具体地，给两个分布都附上**同一个独立坐标**，全变差距离不变：

$$
d_{\mathrm{TV}}(P\otimes R,Q\otimes R)
=\frac12\sum_{a,b}|P(a)R(b)-Q(a)R(b)|
=d_{\mathrm{TV}}(P,Q).
$$

把多个坐标一次换一个，再用三角不等式，便得到

$$
d_{\mathrm{TV}}\!\left(\bigotimes_{t=1}^{s}P_t,\,
\bigotimes_{t=1}^{s}Q_t\right)
\leq\sum_{t=1}^{s}d_{\mathrm{TV}}(P_t,Q_t).
$$

首项的误差至多 $S/H$；后面共有 $s-1$ 个坐标，每个误差至多 $1/(q-1)$。因此

$$
d_{\mathrm{TV}}\!\left(
\operatorname{Law}(Y_I\mid X=x),
\operatorname{Law}(\widetilde Y_I\mid X=x)
\right)
\leq\frac SH+\frac{s-1}{q-1}.
$$

这个界与具体的 $x$ 无关，所以再对 $X$ 的可能取值求平均，也得到同样的无条件界。这里用的是：对相同权重 $w_x$ 混合两组分布时，

$$
d_{\mathrm{TV}}\!\left(\sum_xw_xP_x,\sum_xw_xQ_x\right)
\leq\sum_xw_xd_{\mathrm{TV}}(P_x,Q_x).
$$

把全变差的定义代入，交换求和次序并使用三角不等式即可得到它。此处两边使用的共同权重正是 $\Pr(X=x)$。

现在看参数为何有系数 $6$：

$$
H\geq\frac{6S}{\varepsilon}
\quad\Longrightarrow\quad
\frac SH\leq\frac{\varepsilon}{6},
$$

并且

$$
q-1\geq\frac{6(s-1)}{\varepsilon}
\quad\Longrightarrow\quad
\frac{s-1}{q-1}\leq\frac{\varepsilon}{6}.
$$

两项加起来，得到原文的式 (6)：

$$
d_{\mathrm{TV}}(Y_I,\widetilde Y_I)
\leq\frac{\varepsilon}{6}+\frac{\varepsilon}{6}
=\frac{\varepsilon}{3}.
$$

**特别注意：**我们只用到“给定完整 $X$ 后”的独立性。去掉条件后，所有 $G_e$ 共享随机的旧日历 $X$，一般会相关；不能直接说它们无条件独立。

**把公式展开看一个例子。** 当 $m=4,s=3$，新日历是

$$
D=(U,\ U+G_1,\ U+G_1+G_2,\ U+G_1+G_2+G_3).
$$

四种位置选择对应的记录如下：

| $I$ | 实际的“首日 + 差”记录 $Y_I$ | 理想记录 $\widetilde Y_I$ |
| --- | --- | --- |
| $\{1,2,3\}$ | $(U,G_1,G_2)$ | $(U,G_1,G_2)$ |
| $\{1,2,4\}$ | $(U,G_1,G_2+G_3)$ | $(U,G_1,G_3)$ |
| $\{1,3,4\}$ | $(U,G_1+G_2,G_3)$ | $(U,G_2,G_3)$ |
| $\{2,3,4\}$ | $(U+G_1,G_2,G_3)$ | $(U,G_2,G_3)$ |

例如，$I=\{1,3,4\}$ 时看到的实际日期是 $(D_1,D_3,D_4)$。改写成“首日 + 差”后，第二项是 $D_3-D_1=G_1+G_2$；Step 3 说明它在分布上接近最后一个间隔 $G_2$。$I=\{2,3,4\}$ 时则是把首项 $U+G_1$ 近似换成 $U$。

## Step 5：旧日历的归纳假设终于在哪里用上？

看 Step 4 得到的理想记录：

$$
\widetilde Y_I=(U,G_{i_2-1},\ldots,G_{i_s-1}).
$$

令

$$
E(I)=\{i_2-1,\ldots,i_s-1\}.
$$

因为 $2\leq i_2<\cdots<i_s\leq m$，所以 $E(I)$ 是 $[m-1]$ 中的一个 $(s-1)$ 元位置集。**第一个被观察位置 $i_1$ 已经消失了**：它只影响被随机起点 $U$ 掩盖的前缀；后面每一段保留下来的末尾间隔，其下标是 $i_{t+1}-1$。

为什么说理想记录只由旧记录 $X_{E(I)}$ 决定？设旧记录的一个可能取值是有序向量 $z=(z_1,\ldots,z_{s-1})$。对它使用一套固定的随机规则：

1. 抽取 $U\sim\operatorname{Unif}[H]$；
2. 对每个 $z_t$，独立抽取 $V_t\sim\operatorname{Unif}[q^{z_t}]$；
3. 输出 $(U,V_1,\ldots,V_{s-1})$。

这套随机规则对**每个 $I$ 都完全相同**；输入不同的只是旧日历中选出的 $X_{E(I)}$。未选中的旧指数不影响这些被选间隔的条件分布。

同一套随机规则也叫一个**共同随机核**。对两种输入分布施加同一个随机核，不能增大全变差距离。直观上，对两份数据做相同的随机处理，不会凭空制造更多区分它们的信息。形式上，若 $K(y\mid z)$ 是输出 $y$ 的条件概率，那么

$$
\begin{aligned}
d_{\mathrm{TV}}(PK,QK)
&=\frac12\sum_y\left|\sum_z(P(z)-Q(z))K(y\mid z)\right|\\
&\leq\frac12\sum_z|P(z)-Q(z)|\sum_yK(y\mid z)\\
&=d_{\mathrm{TV}}(P,Q).
\end{aligned}
$$

于是**此处真正调用归纳假设**：

$$
d_{\mathrm{TV}}(\widetilde Y_I,\widetilde Y_J)
\leq d_{\mathrm{TV}}(X_{E(I)},X_{E(J)})
\leq\frac{\varepsilon}{3}.
$$

对任何 $I,J$，把两次 Step 4 的替换误差和这一次旧日历的误差相加：

$$
\begin{aligned}
d_{\mathrm{TV}}(D_I,D_J)
&=d_{\mathrm{TV}}(Y_I,Y_J)\\
&\leq d_{\mathrm{TV}}(Y_I,\widetilde Y_I)
 +d_{\mathrm{TV}}(\widetilde Y_I,\widetilde Y_J)
 +d_{\mathrm{TV}}(\widetilde Y_J,Y_J)\\
&\leq\frac{\varepsilon}{3}
 +\frac{\varepsilon}{3}
 +\frac{\varepsilon}{3}
=\varepsilon.
\end{aligned}
$$

第一行来自 Step 4 的可逆变换；第二行是三角不等式。因为证明从头到尾对任意 $I,J$ 都成立，归纳步完成。

## 一个从头到尾可核对的完整构造：$m=3,\ s=2,\ \varepsilon=1/2$

这个例子会出现很大的数字，但每个数字都有明确用途，也确实符合证明的全部要求。

**先造旧日历。** 归纳需要一份有 $m-1=2$ 个日期、只观察 $s-1=1$ 个日期、误差至多 $\varepsilon/3=1/6$ 的旧日历。根据 Step 1，让 $V$ 在 $\{1,\ldots,6\}$ 上均匀分布，取

$$
X_1=V,\qquad X_2=V+1,\qquad \ell=7.
$$

那么 $d_{\mathrm{TV}}(X_1,X_2)=1/6$。

**再选参数并生成新日历。** 此时

$$
q=1+\left\lceil\frac{6}{1/2}\right\rceil=13,
\qquad
S=2\cdot13^7,
\qquad
H=\left\lceil\frac{6S}{1/2}\right\rceil=12S.
$$

给定 $V=v$，独立抽取

$$
G_1\sim\operatorname{Unif}[13^v],
\qquad
G_2\sim\operatorname{Unif}[13^{v+1}].
$$

再独立抽取 $U\sim\operatorname{Unif}[H]$，设

$$
D=(U,\ U+G_1,\ U+G_1+G_2).
$$

它一定严格递增，且 $D_3\leq H+S$，所以日期范围虽大，却是有限的。

**列出三种观察记录。**

| $I$ | 实际记录 $Y_I$ | 理想记录 $\widetilde Y_I$ | 对应的旧位置 $E(I)$ |
| --- | --- | --- | --- |
| $\{1,2\}$ | $(U,G_1)$ | $(U,G_1)$ | $\{1\}$ |
| $\{1,3\}$ | $(U,G_1+G_2)$ | $(U,G_2)$ | $\{2\}$ |
| $\{2,3\}$ | $(U+G_1,G_2)$ | $(U,G_2)$ | $\{2\}$ |

每种记录与自己的理想记录的距离至多

$$
\frac SH+\frac1{q-1}
=\frac1{12}+\frac1{12}
=\frac16.
$$

理想记录之间的距离至多旧日历的距离 $1/6$。故任意两种观察方式之间的距离都至多

$$
\frac16+\frac16+\frac16=\frac12.
$$

注意表中第一行的实际记录与理想记录完全一样，后两行的理想记录也完全一样；上面的三个 $1/6$ 是为了**统一处理所有位置对**而给出的保守上界。

## 向老师汇报时的讲述顺序

1. **先说归纳变量：**对观察个数 $s$ 归纳，并且同时证明所有 $m\geq s$；归纳步用 $m-1$ 个旧日期构造 $m-1$ 个新间隔。
2. **解释构造直觉：**旧日期 $X_e$ 当作指数，决定间隔 $G_e$ 的尺度 $q^{X_e}$；大随机起点 $U$ 用来掩盖首日之前的前缀和。
3. **点出核心估计：**固定 $X$ 后，一段间隔之和与最后一段的距离至多 $1/(q-1)$；因为严格递增整数指数产生几何级数。
4. **解释记录变换：**把观察日期改写成“首日 + 相邻差”，再把首日换成 $U$、每段和换成末尾间隔。每份记录的替换误差至多 $\varepsilon/3$。
5. **说明归纳落点：**理想记录由 $X_{E(I)}$ 经过同一个随机规则生成，故它们的距离至多旧误差 $\varepsilon/3$。两次替换加旧误差，正好得到 $\varepsilon$。

如果老师追问“这些间隔是否独立”，要准确回答：**给定完整的 $X$ 后独立；无条件下不一定独立。** Step 3 和 Step 4 都是先在这个条件下估计，再对 $X$ 求平均。
