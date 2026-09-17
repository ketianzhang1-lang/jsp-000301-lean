import Tables

namespace JSP000947
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem c4_7_0 : checkTree (fun t => passes rows4 262163 (2145 * t)) 7 2 = true := by
  decide +kernel

theorem certificate4 : checkTree (fun t => passes rows4 262163 (2145 * t)) 7 2 = true :=
  c4_7_0

end JSP000947
