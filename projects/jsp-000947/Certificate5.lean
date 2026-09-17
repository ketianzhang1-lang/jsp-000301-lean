import Tables

namespace JSP000947
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem c5_10_0 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 7 = true := by
  decide +kernel

theorem c5_10_1 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 1031 = true := by
  decide +kernel

theorem c5_10_2 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 2055 = true := by
  decide +kernel

theorem c5_10_3 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 3079 = true := by
  decide +kernel

theorem c5_10_4 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 4103 = true := by
  decide +kernel

theorem c5_10_5 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 5127 = true := by
  decide +kernel

theorem c5_10_6 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 6151 = true := by
  decide +kernel

theorem c5_10_7 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 10 7175 = true := by
  decide +kernel

theorem c5_11_0 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 11 7 = true :=
  checkTree_join 10 7 c5_10_0 c5_10_1

theorem c5_11_1 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 11 2055 = true :=
  checkTree_join 10 2055 c5_10_2 c5_10_3

theorem c5_11_2 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 11 4103 = true :=
  checkTree_join 10 4103 c5_10_4 c5_10_5

theorem c5_11_3 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 11 6151 = true :=
  checkTree_join 10 6151 c5_10_6 c5_10_7

theorem c5_12_0 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 12 7 = true :=
  checkTree_join 11 7 c5_11_0 c5_11_1

theorem c5_12_1 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 12 4103 = true :=
  checkTree_join 11 4103 c5_11_2 c5_11_3

theorem c5_13_0 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 13 7 = true :=
  checkTree_join 12 7 c5_12_0 c5_12_1

theorem certificate5 : checkTree (fun t => passes rows5 268435485 (40755 * t)) 13 7 = true :=
  c5_13_0

end JSP000947
