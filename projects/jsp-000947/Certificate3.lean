import Tables

namespace JSP000947
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem c3_5_0 : checkTree (fun t => passes rows3 4109 (165 * t)) 5 7 = true := by
  decide +kernel

theorem certificate3 : checkTree (fun t => passes rows3 4109 (165 * t)) 5 7 = true :=
  c3_5_0

end JSP000947
