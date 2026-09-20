# JSP-000554：独立语义与提交材料复核

**本文件为执行前静态复核记录：已核对的是 prime-gap 索引的自然密度一，原题范围并未被有限反例替代。新的隔离执行结果仍须由最终原始证据确认。**

## 固定对象与原题

- JSP-000554 / Erdős 682；PR #369，claim #1577；awards head `388fbf61e647ea2a4a10e8d78344cb7688cf48c4`。
- 证明 `ketianzhang1-lang/jsp-000301-lean`，branch `jsp-000554-residue-reduction`，commit `21fcf006fd68b0bead9f979b704c92032f05cba8`，project `projects/jsp-000554`。
- 入口 `JSP000554.jsp_000554`，`JSP000554Complete.lean`。PR catalog 只修改该题 Lean proof + Attribution basis；`66542c86a00ecedf4d59bd3df0a6c05748e48cb2` README/说明链接是历史文档版本，不是第二份选定证明。
- 最新官方 lean-verify rules：awards `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`。

成功读取原始 [Gafni–Tao, Rough numbers between consecutive primes, equation (1.1), Theorem 1.1 及其后讨论](https://arxiv.org/html/2508.06463v1#S1)，并核对 Section 4 的 residue 定义。研究问题是：相邻质数的开区间中，具有最小质因子至少等于 gap length 的整数存在于几乎所有 prime gaps；例外的**索引比例**趋于零。论文定量定理推出此结论。主目录简短问句不应误读为对每一个 gap 全称成立。

不将密度一改写为“存在无穷多个好 gap”或“所有充分晚 gap 都好”；单个有限反例只能驳斥另一个更强的全称命题，不能证明这个密度结论。原始 Erdős 网站本轮直读 403，故来源核实以已成功读取的原始论文为依据。严格 `minFac(m) > gap` 是 Remark 1.1 另外讨论的较强版本，本申请采用 equation (1.1) 的非严格 `>=`。也不声称定量最优误差项、条件性常数或无穷多坏 gap。

| 数学要求 | 定义与目标 | 语义核对 |
|---|---|---|
| 真正的相邻质数，全体 gap 索引 | `Erdos682.nthPrime := Nat.nth Nat.Prime`；`nthPrime_prime`, `nthPrime_lt_succ`, `no_prime_between_nthPrime` | 使用 Mathlib 标准 Prime；n 从 0 起，gap 2–3 的索引亦包含 |
| 区间内实际整数 m 与实际最小质因子 | `Nat.minFac m`；`GoodGap`, `mem_goodGapIndices_iff` | 两端严格不等，故 m>1；least factor 的 primality、divisibility 和最小性另加独立 bridge |
| 自然数减法真实表示 gap | `lower_add_gap` | nthPrime 严格增长，故 Nat.sub 没有造成截断丢失 |
| endpoint BadGap 与例外索引恰好相同 | `badGap_iff_exceptional`, `badGapIndices_eq` | 两端质数和中间无质数均从枚举证明，不是额外假设 |
| 好索引自然密度一 | `goodGapIndices_density_one`, `goodGap_count_ratio_tendsto` | 普通 Tendsto，分母是索引数 N；不是 prime values 的自然密度、上密度或仅某一子序列 |
| 坏索引自然密度零 | `badGapIndices_density_zero`, `badGap_count_ratio_tendsto` | 按 n=0,…,N−1 的真实 filter cardinality，极限为 0 |
| 每个 h≥2 的 residue 必要充分条件 | `badGap_iff_residue_all`, `exceptional_iff_residue` | h≤p、p.Prime、(p+h).Prime 保留；只凭 residue membership 不推出无限质数对 |
| 保留原有有限分类与精确计数 | 原 23 targets 与 `jsp_000554` 第二合取项 | h=2,4,6,8,10,12 完整表和任意有限 s 的计数，未代替无限密度部分 |

第一 gap 是空开区间；包括它并不要求它是好 gap。有限坏索引不妨碍密度一。筛选 `Finset.range N` 明确只含 N 个索引；N=0 的除法约定不影响 atTop 极限。

## 依赖闭包与独立桥梁

阅读原始 JSP000554、完整集成模块、AuditComplete、pinned Erdos682 约 216 KB 主模块及 Util/Density。上游 HasDensity 定义为实际有限前缀比例的普通极限。密度定理链为 `erdos_682` → `exceptionalGapIndices_density_zero` → `exceptionalPrefixCount_isLittleO`，其中 all-index 结论由 dyadic estimates、单调覆盖及素数尺度转换实证取得；`HasDensity` 并非被直接当作定理参数假定。主定理无 Hardy–Littlewood 假设；上游另外有条件性声明不会因此变成无条件最优常数结论。

七项 auditor bridges 使用原始 Mathlib `Nat.nth Nat.Prime`、`Nat.minFac`，并直接定义 `RoughGap` 和 `(Finset.range N).filter` 的好/坏数量：相邻端点、实际 least-factor 规格、好坏 predicate correspondence、literal count 两个极限、包含素性前提的 residue 等价。它们在外部审计文件单独编译，不改原证明。

## 执行计划与真实边界

精确 Lean 4.34.0；Mathlib `5ed2965256430c3649e86755f9576b54eca72435`，九项依赖锁定。UPSTREAM.json 固定 51 个来源文件的原始 Git blob、SHA-256、精确 compatibility renames/edits/notice、port SHA-256。原 verify_complete.py 干净编译 54 模块并审计 37 条原 targets（不使用 --resume）。Kernel prefixes 包含 PrimeNumberTheoremAnd、UnitFractions、ErdosProblems、Util、JSP000554、JSP000554Complete；负对照必须拒绝 1=0；原始模块 SHA 要求保持不变。原 finite Python crosscheck 为附加一致性检查，不能替代 Lean 证明。

本次官方 targets manifest 共 44 项 = 37 原目标 + 7 bridges。两个上游目标以已配置 AuditComplete 为 tracked verification entry，并记录真实 ErdosProblems/Erdos682.lean port hash；干净 verifier 必须编译并 replay 实际源模块。原始 `.lean` / Lake 配置不改变，官方 audit.py 不改。

本代理没有本机执行任何 Lean/Lake/verifier。实际完成状态由隔离非 root Docker/GitHub Actions 的命令、退出码、完整日志、strict standard-axiom allowlist、kernel replay 与 NaNoda raw evidence 决定；有阶段失败就保留失败，不使用历史运行替换本次结果。

## 原创、归属及发现的文件缺口

`JSP000554.lean` 与最初 proof revision `2a6c737b5fb409a5600918cc5a2bab0a8dd174bb` 逐字节相同；SHA-256 均为 `bb32c64b879462a8e70041a6b64d5a1e3a9022a2b8830668c119eff9430f9ff7`。个人新增的是 23-theorem finite residue formalization、12-theorem statement/count integration 及 port/verification；完整 analytic proof 是复用 plby 的 Codex/GPT-5.6 Sol 工作。Gafni/Tao 数学贡献、Formal Conjectures/PrimeNumberTheoremAnd/UnitFractions/Mathlib 等逐文件贡献保留。不声称全球首形式化、数学发现或上游 proof 自己原创。

**发现并已修正的材料问题**：选定版本及修正前的 branch tip `068f83db9a9d091f2a3d5d8b6bd99488ce18fcc3` 的 PROVENANCE 说项目 `LICENSE` 包含 Apache 2.0，但该文件不存在；仓库根 LICENSE 是 MIT。UPSTREAM-LICENSE 仅提供 Apache 地址，源头 Apache 通知保留。已在 `proposed-docs/` 准备完整 APACHE-2.0.txt 与准确的 PROVENANCE 修订，已由父任务发布 documentation-only commit `12d4f4f213e16d00773d446d7d4df6f09efd54bd` 并逐字节读取回核对两个文件；选定证明 `21fc...`、源码和依赖不变。完整 Apache 文本取自现有725的固定版副本，sha256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`，并对照 [Apache 官方全文](https://www.apache.org/licenses/LICENSE-2.0.txt) 核读。替换稿已链接实际发布的修正 PROVENANCE 和 Apache 文本；原历史文件本身没有改变。

当前 proof commit README 的“verification in progress”是当时静态说明；后来66542的 README/VERIFICATION和本次最终报告是分立的执行记录，不将旧 README 当作最新运行结果或另一个proof SHA。

2026-09-20 重新读取相关 #1133/#1130、#829、#1116、#1306，均仍开放。前几项为 finite examples/counterexamples，后者登记既有完整上游且不索取其作者身份；全稿保留这些重叠，不自动决定任何申请者奖金资格。

新版 PR 补完整 formal-statement/solver registration/self-check 四判断/JSON/命令条目；claim 补 Merged submission PR 字段并明确未合并。pre-opening 历史条件和 merged declaration 保持未勾选，身份验证、候选登记和主办方审核不冒充已完成。
