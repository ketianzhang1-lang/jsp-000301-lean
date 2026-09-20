# JSP-000465：完整反例及遗漏补充版本审阅

**当前结论：证据不足（等待两个固定版本的本轮实际检查）。** 静态语义审阅确认完整紧致性反例以及更强的自适应选择补充均有无额外假设的终点。本轮还发现旧 PR 正文没有列出题库 diff 已提交的补充版本，必须补齐并独立核验，不能只验证基础版本。

| 必答判断 | 当前结论 | 决定性材料 |
| --- | --- | --- |
| 证明对象是否为指定原题？ | 是，静态对应确认 | 原始论文 Ch10 Thm1.1；固定、非空、有限、连通、二部且每个成员有圈的反例 |
| 指定 commit 是否实际验证通过？ | 两组均待本轮验证 | 基础 `6a793...` 13 项；补充 `78dbc...` 21 项 |
| 是否完整解决原题？ | 代码覆盖完整；执行后定论 | 常数与宿主阶数的量词顺序正确，同时排除更强的无森林版本 |
| 是否满足 Lean 完整性要求？ | 暂无法确认 | 等待原样构建、完整依赖闭包、公理、内核与独立 checker |

## 版本和原始来源

PR [442](https://github.com/TheJustinSunPrize/awards/pull/442)，claim [1572](https://github.com/TheJustinSunPrize/awards/issues/1572)。PR snapshot base `ff33abd13163e789790eb1014e55f57c05f94432`、head `de18e5d8fa57cdfd064bb18aa75f4b9983858590`、分支 `jsp-000465-verified-kz`。只修改一份题库文件的 Lean proof 与 Attribution basis。原题描述、Current status 与 Eligible to claim 保持不变。

| 组 | 分支、完整 SHA | 范围 |
| --- | --- | --- |
| 465 | `jsp-000465-verified-kz`, `6a793b157c1afdf29f3e6bbbf3cf514535d1dfca` | 七个原审计闭包、八个模块的完整基本提交 |
| 465-uniform | `jsp-000465-uniform-ratios-20260919`, `78dbc684a1ce3d392b150d98bdc5b94a9269f3e3` | 保留原完整提交，增加五条比例/自适应选择定理；原文件与原 pin 逐字节比较 |

共同仓库 `ketianzhang1-lang/jsp-000301-lean`，项目 `projects/jsp-000465`。文档 commit `cafcabe...` / `07e3ce6...` 不替代两个实际证明 commit。

[Erdős 575](https://www.erdosproblems.com/575) 页面本次直接读取返回 403；题库原始引用的 [OpenAI, Ten Advances, Chapter 10, Theorem 1.1](https://cdn.openai.com/pdf/ten-proofs-oai.pdf#page=241) 已实际读取。PDF 页码 241（印刷页237）说明有限非空且每个成员含圈的修正版；反例更强地使所有成员连通、二部。数学原文给出的 family 上界是 O(n^(21/16))，各成员下界 Ω(n^(4/3))，两指数相差 1/48。此处的 compactness 是极值图论的常数因子缩并，不是把另一个拓扑紧致性命题拿来替换。

## 覆盖矩阵与独立桥梁

| 原题要求 | 声明或定义 | 语义检查 |
| --- | --- | --- |
| 所有有限简单图 | `Erdos180.FiniteGraph` = 自然阶数及 `SimpleGraph (Fin order)` | 每个有限图可重标号；禁止成员固定，但宿主 n 任意 |
| 普通子图避免 | `FamilyFree`; `Verify465.literalExtremal` | 逐成员调用 Mathlib `SimpleGraph.Free`，不是诱导避免；最大化整个标号图有限集的 edgeFinset.card |
| 真正的极值与单图约定 | `familyExtremal_singleton`, `familyExtremal_attained`；两个 literal 桥梁 | 与 Mathlib 单图 extremalNumber 相等；所有 n 包括零都有真实 admissible maximizer，排除空类默认 sup 问题 |
| 非空有限 family 在先 | `connected_bipartite_counterexample` | ∃F 后才是 ∀K>0；每个成员 Connected、IsBipartite、¬IsAcyclic，不借助便宜的森林反例 |
| 严格同时分离 | `uniform_separation`；`connected_cyclic_counterexample_literal` | ∀K>0∃N∀n≥N∀H∈F，K ex(n,F)<ex(n,H)。N 在 H 之前，一个阈值控制全部成员 |
| 两种紧致性问题完整否定 | `not_bipartite_compactness`, `not_erdos_180_source`；两个 literal 桥梁 | 同时反驳题库“至少一个二部成员”的一般版本和原论文排除森林的强化版本 |
| 比例分母确实为正 | `eventually_member_positive`, `uniform_ratio_small` | 所有成员的 extremalNumber 在共同阈值之后正；分式不是依赖 Lean 对除零的约定 |
| 任意变动的成员选择 | `adaptive_ratio_tendsto`, `no_adaptive_comparison`, `adaptive_compactness_counterexample` | σ:Nat→FiniteGraph 完全任意，只最终在 F 中；无单调或固定选择假设；极限沿 Nat atTop 到 Real 的通常 nhds 0 |

基本文件六条本地定理调用七个带归属的完整上游模块，核心上界和下界并未作为结构字段或类型类假设输入。统一分离取 ε=c/(2K)，结合固定 c>0 的逐成员下界，通过有限性合并 eventual 条件。新 supplement 的比例用 ε^{-1} 倍严格分离，正分母允许转成比值；自适应选择只在共同阈值后代入 σ(n)。没有证明最优指数、最小 family 大小或新数学构造。

## 本轮执行清单

- 基础 `465-targets.json`：七个原 verifier 目标 + 六个独立桥梁 = **13 项**。原 verifier 干净 `lake build --wfail` 覆盖七上游模块和 JSP000465；合并 `leanchecker.log` 必须出现八个真实重放标记；直接检查 Audit.lean 的七个闭包、九个依赖 revision 和负控制。
- 补充 `465-uniform-targets.json`：原+补充共十二个目标 + 九个独立桥梁 = **21 项**。`verify_supplement.py` 先对比基础 commit 的全部 Lean/工具链/manifest 字节，再重新跑原验证，明确编译/重放 `JSP000465Uniform`，检查十二个闭包及新的负控制。
- 新补充模块不在原 Lake roots 中。仅对精确 `lake build +JSP000465Uniform` 提供已披露的人工等价编译 adapter；每次都由实际固定 Lake 调用固定 Lean，以 `-DwarningAsError=true -j1 -M12000` 编译真实源文件，删除旧 olean，记录源前后 hash、命令、输出 hash、退出码及新 olean。其他命令原样传递。不得称其为原生 Lake target 成功，不改 proof、lakefile 或官方 audit.py。
- 两个组均需完整独立桥梁、公理传递闭包、标准三公理硬白名单 NaNoda、依赖实际 revision、源前后 hash 检查。Lean4.34.0，Mathlib `5ed2965256430c3649e86755f9576b54eca72435`；exporter 的4.34兼容重建如实披露。没有在本地执行 Lean/Lake。

## 归属与许可

原完整数学和形式证明属于 OpenAI/Astra 及源头署名作者；原来源 [openai/ten-proofs@a13547c6be4563746881d0b3b4c9fd03f72f0484](https://github.com/openai/ten-proofs/blob/a13547c6be4563746881d0b3b4c9fd03f72f0484/CompactnessAndDegeneracy.lean)。直接七模块来源为 [plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos180)。Apache-2.0 及源头 headers 保留，兼容 port 由 PORT.patch / UPSTREAM_SHA256SUMS 明确标出；本地接口和 supplement 署提交者及 ChatGPT/Codex 辅助。既有上游 linter 设置保持原样，不把关掉 linter 当作消除证明缺口。

PR40 / Issue44 已登记原证据；Correction58 / withdrawn59 明确说明打包不产生独立核心证明作者身份；相关 JSP174 复用同一 OpenAI 发展，不对同一贡献重复领款。PR401 是带森林的不同范围，不能替代本案更强 counterexample。当前40、44、401 open，58、59 closed，正文已读取；未据此推断主办方受理或奖项资格。

## 需要修订的提交材料

旧 PR 正文及 claim 没有说明题库已选择的 `78dbc...` supplement，这是实质性版本遗漏。本次给两个 JSON proof records，并在 PR 详细解释新增五定理、两份实际检查和人工等价编译限制。claim 只指向同一 PR 的证明资料，不重复上传证据或开新申请。

其余补全包括最新模板所需原始问题来源、formal-statement 来源与固定位置、先数学审核/solver 注册流程、四个明确自查判断、完整 source/dependency/axiom audit 链和 merged PR 栏位。原 PR 打开前完成新版自查的历史条件不能补造，相关框保持未勾选；merged PR 亦保持未勾选。官方数学审核、solver 注册、身份/归属核验和授奖决定仍待确认。
