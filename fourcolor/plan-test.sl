; slc std/macro.sl std/nat.sl std/list.sl fourcolor/ring.sl fourcolor/defs.sl fourcolor/orient.sl fourcolor/base.sl fourcolor/sweep.sl fourcolor/geo.sl fourcolor/plan.sl fourcolor/plan-test.sl --goal proved
(def-adts $ (PlanThm : -> Type)
  enum
  (many MkPlanThm : (erased (Level) L)
      (erased (Fn L (erased (List (Edge)) es) (erased (Drawing es) d) -> (erased (SweepPlan es) p)) thm)
      -> (PlanThm)))

(goal erased (PlanThm))
(qed (MkPlanThm (level-of drawing-plan) drawing-plan))
