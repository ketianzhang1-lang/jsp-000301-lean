import Tables

namespace JSP000947
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem c2_7_0 : checkTree (fun t => passes rows2 1035 (15 * t)) 7 2 = true := by
  decide +kernel

theorem certificate2 : checkTree (fun t => passes rows2 1035 (15 * t)) 7 2 = true :=
  c2_7_0

end JSP000947
