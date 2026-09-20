# JSP-000725：独立语义与提交材料复核

**本文件为执行前的静态复核记录：原题对应和完整范围已核对；新的隔离构建、公理审计、kernel replay 与 NaNoda 结果须以最终证据报告为准。本文件不将计划执行的检查标为通过。**

## 固定对象

- 原题：JSP-000725 / Erdős 874；PR #361，claim #1412。
- awards head：`8765191628536b03c5f7e6265fadae15678f35b7`。当前差异仅修改该条目的 Lean proof 和 Attribution basis（2 additions / 1 deletion），不改写原题。
- 证明仓库：`ketianzhang1-lang/jsp-000301-lean`；branch `jsp-000725-interval`；commit `d0d37952bba030d7c8a68f000094e0d601d9fed7`；project `projects/jsp-000725`。
- 完整入口：`JSP000725.jsp_000725`，`JSP000725Complete.lean`。文档链接 `5a83c4c7822c43a65d22e894595514f841d76609` 是另行固定的历史说明，并非第二个待验证证明版本。
- 官方 lean-verify：awards `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`；父任务已重新核查其仍为当前规则。

## 从原始文献建立要求

阅读 [Deshouillers–Freiman, On an additive problem of Erdős and Straus, 2, Astérisque 258 (1999), pp. 141–142](https://www.numdam.org/article/AST_1999__258__141_0.pdf#page=3)。摘要和引言定义 admissibility：不同正数目、互异元素的和层彼此不交；Theorem 1 给出充分大 N 时任意 admissible A⊆[1,N] 的界。Straus 顶端连续区间给出匹配下界。由此原问题的极值函数具有渐近常数 2；这里的最终精确式是 `floor(sqrt(4N+1))−1`。

原文宣告某个有效可计算阈值的存在，但本申请没有声称输出具体数值阈值；原来的极值渐近问题不要求给出一个数值。原文后续关于特殊 N 下极大集唯一性的讨论不构成当前题目的额外子问。ErdosProblems 网站此轮直接访问返回 403，故不以无法获取的页面内容作新证据；原始论文已成功读取。

| 原题要求 | 选定 Lean 入口 | 独立审查结果 |
|---|---|---|
| 正整数集合 A⊆{1,…,N}；互异求和项 | `Admissible`, `Icc 1 N` | 用 Finset 的子集表示不重复求和项；没有多重集、负整数或零元素的替换 |
| 相同和决定项数；子集可重叠 | `admissible_iff_cardinality_determined`, `admissible_iff_upstream` | 原始自然数版本也包含空子集；在正元素条件下，非空和严格正，已证明其与上游仅正层版本等价 |
| ℕ、ℤ 模型没有丢失 admissible 集合 | `card_toInt`, `sum_toInt`, `bounded_iff`, `exists_nat_preimage` | 前向 Finset.map 保和、基数；逆向 Int.toNat 在正区间内确为逆 |
| 最大值涵盖所有 admissible 集合 | `admissibleFamily`, `maxCard`, `maxCard_eq_upstream` | `Icc 1 N` 全 powerset 经完整谓词筛选后 sup 基数；未限制为区间或作者构造 |
| 每个 N 的匹配下界 | `terminalInterval_spec`, 原始 `construction_for_every_N` | `N=0` 合法为空集合；自然数截断减法的长度可行性另行证明 |
| 任意 admissible 集合的最终上界及极值可达 | `eventual_maxCard_exact`, `eventual_terminalInterval_optimal` | 阈值位于 A 的量词外，N 足够大后对全部 A 一致；不是依赖 A 的阈值 |
| 真正极值函数的归一化极限 2 | `maxCard_asymptotic` | 分母为 `Real.sqrt N`；普通 atTop 实极限；N=0 的定义不影响极限 |

没有将“每个 N 存在下界构造”误述为“每个 N 精确最优”。没有声称所有极大集分类或全小 N 的极值公式。

## 依赖链与无循环假设审查

阅读本地三个证明模块和 AuditComplete，并独立取得固定上游 `Erdos874.lean`、Foundations、Structure、EndpointOrientation、ExactUpper、Tail、Asymptotics。关键链为：`jsp_000725` → 原作者 all-N interval construction + `maxCard_eq_upstream` → `erdos_874_eventual_exact` / `erdos_874` → `eventually_maximizers_density_endgame hasEventuallyLargeSetStructure`。`HasEventuallyLargeSetStructure` 虽作为中间引理的参数存在，最终由 `hasEventuallyLargeSetStructure` 定理实证提供，未被作为最终入口的未证前提；结构定理继续由有限证书构造证明。静态查看的入口没有自定义公理、native_decide 或 skipKernelTC。完整传递闭包仍须由实际 axiom/kernels/export 审计确认，静态字符串检索本身不作通过凭证。

六个 auditor bridge 逐一定义和核查：literal `Admissible`、all-N witness、独立 powerset `maximum` 与实际 maxCard 的相等、arbitrary-set eventual bound、eventual attained maximum、sharp asymptotic。它们是另行提供的审计输入，不写入原证明快照。

## 可复现执行计划

Lean 4.34.0，Mathlib `5ed2965256430c3649e86755f9576b54eca72435`；全部九个依赖由 lake-manifest 锁定。bootstrap 固定 42 个外部源码的原始 Git blob、SHA-256、精确修改与最终 SHA-256。原 verifier 无 `--resume` 时显式编译 42 upstream + 3 local proof + 1 audit = 46 个模块，原有 28 条 axiom targets 均包含在新 manifest 中。Kernel prefixes：ErdosProblems、JSP000725、JSP000725Bridge、JSP000725Complete；有必须被拒绝的 `(1:Nat)=0` 负对照。

manifest 共 34 项 = 28 original + 6 auditor bridges。原 Bridge 模块不是当前 Lake 原生 root，故其目标经已配置的 AuditComplete 导入入口审计，另记录实际 definition_source 及其 SHA-256；两个下载的上游主定理同样记录真实来源及 port SHA。此路由不表示定义在 AuditComplete，不修改 Lake 文件，也不跳过实际声明的 print/axiom 检查。原 verifier 将实际定义模块干净编译、kernel replay 后才执行官方 audit。

本代理没有在本机执行 Lean、Lake 或证明 verifier。父任务将使用隔离、无网络的非 root Docker/GitHub Actions 完成所有实际检查，公开原始退出码、目标、公理、依赖与独立 checker 证据。

## 贡献、许可证与材料修正

原始 `JSP000725.lean` 与 `a197ebc6cc3ea878c60db0f2456465cef1e8e09b` 的文件逐字节相同；两者 SHA-256 均为 `a3c0add755c8df4967e688693e7024610965b623d803127abbf72b287f6b1e2a`。作者贡献是原始区间构造、自然/整数精确桥梁、极值函数桥梁、最终最优性的集成和验证；上游完整 upper proof 不是自己的原创。保留 Straus、Deshouillers–Freiman 的数学信用，plby 分发上游的 Codex / GPT-5.6 Sol 形式化信用，以及 Boris Alexeev 等逐文件版权。项目自带 UPSTREAM-LICENSE.txt 和完整 APACHE-2.0.txt；仓库根 MIT 不替换外部文件许可证。

2026-09-20 重新读取：sumo166 的 #678 部分区间构造记录、CHENLexiao8848 的 #730 完整上游归属验证均仍开放。既有上游完整形式化的存在独立披露，不以其是否申请奖金为转移。

新 PR 全稿补全最新要求：明确原始数学证据、待确认 solver registration、submitter-proposed statement、固定证明 JSON、同声明 proof bridge、可复现命令、单一 verification-evidence 插槽和历史 pre-opening 未完成声明。Claim 使用新版 Merged submission PR 字段并明确未合并，proof evidence 仅放 PR；不声称首创、身份已认证、eligible 已改或主办方已接受。
