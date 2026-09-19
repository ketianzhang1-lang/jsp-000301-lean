# 新版 lean-verify：提交者自查操作说明

适用规则固定于官方仓库 `38e63c424c7196f8d4ceb664c5c25f0c0529d5e2`，检查日期为 2026-09-19。官方入口：[lean-verify](https://github.com/TheJustinSunPrize/awards/tree/38e63c424c7196f8d4ceb664c5c25f0c0529d5e2/skills/lean-verify)。以后规则更新时，应重新比较内容，而非仅沿用本说明。

## 自查要交付什么

不是只运行一个叫 `lean-verify` 的命令，也不是把旧 CI 绿灯贴到 PR。新版是一套验证流程，最终应有：

1. 固定的原题、awards PR head 和证明仓库 commit，三者分别记录。
2. 从原题独立列出的要求，以及要求到 Lean 定理的覆盖表。
3. 每个固定工程对应的 `targets.json`，包括所有声称完成的定理和新增的语义桥梁。
4. 匹配固定工具链的隔离环境、干净构建、显式源码检查及完整命令日志。
5. 每个目标的 `#check`、`#print`、`#print axioms`，再尝试 kernel replay 和兼容的外部 checker。
6. 自包含报告，明确回答题意是否对应、指定 commit 是否实际通过、是否完整解决、是否满足 Lean 完整性要求。

只提交数学论文或解题者信息时不要求 Lean 自查；同时提交数学解答和形式化时，自查只处理 Lean 部分。

## 正确顺序

**先固定输入。** 读取 PR 正文、全部 diff/文件、commits、评论及 review；证明仓库可能与 awards 仓库不同。检查正文、题库和评论是否指向不同版本。每个声称完成的版本都要独立核验，不能用新分支的成功替换旧 commit 的结果。

**再核对数学。** 展开定义、所有显隐式参数和实例；检查量词、边界、额外假设及是否可能空集取下确界造成假象。可以独立写出 `IntendedStatement` 并用提交定理证明它，但不能只给可疑定义换个名字。人工题意审阅仍是必要步骤。

**随后实际执行。** 在无凭据、限制可写目录的容器中下载固定依赖，然后断网核验。先清除本工程生成文件，完成原样构建，再运行官方脚本；可信依赖缓存可以复用，但要记录来源和实际 SHA。不要为了跑通而更换 Lean/Mathlib 版本，然后把修补版结果记在原提交上。

官方脚本的最小调用形式如下，路径应指向固定版本的官方脚本与该工程清单：

```bash
python3 /path/to/official/skills/lean-verify/scripts/audit.py preflight /path/to/targets.json --out /path/to/evidence/preflight
python3 /path/to/official/skills/lean-verify/scripts/audit.py run /path/to/targets.json --out /path/to/evidence/audit --lake /absolute/path/to/lake --timeout 300
```

`preflight` 不执行项目证明，也不确认隔离安全；`run` 的成功只说明清单内机械检查达到了该级要求，不证明清单没有遗漏原题义务。它们都不替代干净构建、语义审阅或独立 checker。

**最后写结论。** 使用“验证通过 / 有条件通过 / 部分覆盖 / 验证失败 / 证据不足”之一，并解释决定性证据。标准的 `propext`、`Classical.choice`、`Quot.sound` 可说明为经典 Lean 基础；`sorryAx`、未证明数学公理、循环假设属于缺口。网络失败、检查器不兼容或资源耗尽不能直接写成数学反例。

## 这次前两名的具体安排

| Submission | 固定版本数量 | 清单目标数 | 额外语义检查 |
|---|---:|---:|---|
| JSP-000391 / PR 293 | 1 | 14 | 从论文重新写递推和数字定义，检查下标、系数、归一化、所有进制和移位区间 |
| JSP-000438 / PR 408 | 2 | 13 + 10 | 直接写图与补图的树嵌入，展开 Ramsey 下确界集合，检查偶数阶星图最优性及多色扩展 |

可复现代码位于证明仓库分支 `lean-verify-top2-20260919` 的 `verification/top2/`，工作流位于 `.github/workflows/lean-verify-top2.yml`。具体结果以同包 `report.md` 和运行原始证据为准，本文不是结果证明。

## 如何更新 submission

在 PR 中给出自查日期、完整 proof SHA、报告固定链接、工作流及日志链接、精确覆盖范围和剩余限制。保留数学贡献与形式化贡献的区别。

现有 PR 是早于本次自查打开的，因此不能勾选或声称“打开原 PR 之前已经执行新版自查”。应明确是补做，并请维护者决定现有提交如何适用新版流程。数学解答审核、解题者候选登记、Lean 候选登记及领取奖项仍是独立步骤；自查报告不能替代它们。
