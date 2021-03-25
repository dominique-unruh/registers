theory Compatibility_Tac_Experiments
  imports Laws
begin


subsection \<open>Heterogenous variable lists\<close>

(* TODO: should not be axioms (or not be here) *)
typedecl 'a untyped_lvalue
axiomatization make_untyped_lvalue :: \<open>('a,'b) maps_hom \<Rightarrow> 'b untyped_lvalue\<close>
  and compatible_untyped :: \<open>'b untyped_lvalue \<Rightarrow> 'b untyped_lvalue \<Rightarrow> bool\<close>
axiomatization where
  compatible_untyped: \<open>compatible_untyped (make_untyped_lvalue F) (make_untyped_lvalue G)
    \<longleftrightarrow> compatible F G\<close>

inductive mutually_compatible :: \<open>'a untyped_lvalue list \<Rightarrow> bool\<close> where
  \<open>mutually_compatible []\<close>
| \<open>mutually_compatible vs \<Longrightarrow> list_all (compatible_untyped v) vs
    \<Longrightarrow> mutually_compatible (v#vs)\<close>

inductive compatible_with_all :: \<open>('a,'b) maps_hom \<Rightarrow> 'b untyped_lvalue list \<Rightarrow> bool\<close> where
  \<open>compatible_with_all _ []\<close>
| \<open>compatible_with_all v ws \<Longrightarrow> compatible_untyped (make_untyped_lvalue v) w \<Longrightarrow> compatible_with_all v (w#ws)\<close>

lemma l1:
  assumes \<open>mutually_compatible (make_untyped_lvalue a # as)\<close>
  shows \<open>compatible_with_all a as\<close>
  using assms apply cases apply (induction as)
   apply (simp add: compatible_with_all.intros(1))
  using compatible_with_all.intros(2) mutually_compatible.cases by fastforce

lemma l2:
  assumes \<open>mutually_compatible (a # as)\<close>
  shows \<open>mutually_compatible as\<close>
  using assms mutually_compatible.cases by blast

lemma l3:
  assumes \<open>compatible_with_all b (a # as)\<close>
  shows \<open>compatible_with_all b as\<close>
  using assms compatible_with_all.cases by auto

lemma l4:
  assumes \<open>compatible_with_all b (make_untyped_lvalue a # as)\<close>
  shows \<open>compatible b a\<close>
  using assms compatible_untyped compatible_with_all.cases by blast

lemma l4':
  assumes \<open>compatible_with_all b (make_untyped_lvalue a # as)\<close>
  shows \<open>compatible a b\<close>
  using assms compatible_sym l4 by blast

nonterminal untyped_lvalues
syntax "_COMPATIBLE" :: "args \<Rightarrow> 'b" ("COMPATIBLE '(_')")
syntax "_LVALUE_LIST" :: "args \<Rightarrow> 'b" ("UNTYPED'_LVALUE'_LIST '(_')")
syntax "_insert_make_untyped_lvalue" :: "args \<Rightarrow> 'b"

translations "COMPATIBLE (x)" == "CONST mutually_compatible (UNTYPED_LVALUE_LIST (x))"
translations "UNTYPED_LVALUE_LIST (x)" => "CONST make_untyped_lvalue x # CONST Nil"
translations "UNTYPED_LVALUE_LIST (x,xs)" => "CONST make_untyped_lvalue x # UNTYPED_LVALUE_LIST (xs)"

named_theorems compatible_lvalues

ML \<open>
fun show_compatibility_fact ctxt x y = let
  val facts = case Proof_Context.lookup_fact ctxt \<^named_theorems>\<open>compatible_lvalues\<close>
              of SOME {thms=thms, ...} => thms | NONE => error "internal error"
  fun show fact = let 
    val list = case Thm.prop_of fact of Const(\<^const_name>\<open>Trueprop\<close>,_) $ 
                (Const(\<^const_name>\<open>mutually_compatible\<close>, _) $ list) => list
                | _ => raise TERM("show_compatibility_fact 1",[])
    val list = HOLogic.dest_list list
    val list = map (fn t => case t of Const(\<^const_name>\<open>make_untyped_lvalue\<close>, _) $ x => x 
                     | _ => raise TERM("show_compatibility_fact 2",[])) list
    val index1 = find_index (fn v => v=x) list
    val _ = if index1 = ~1 then raise TERM("show_compatibility_fact 3",[]) else ()
    val index2 = find_index (fn v => v=y) list
    val _ = if index2 = ~1 then raise TERM("show_compatibility_fact 4",[]) else ()
    val _ = if index1 = index2 then raise TERM("show_compatibility_fact 5",[]) else ()
    val swap = index1 >= index2
    val (first,second) = if swap then (index2,index1) else (index1,index2)
    fun show'' 0 fact = let
          (* val _ = \<^print> (fact) *)
          val fact = (if swap then @{thm l4'} else @{thm l4}) OF [fact]
          in fact end
      | show'' pos fact = let
          (* val _ = \<^print> (pos, fact) *)
          val fact = @{thm l3} OF [fact]
          in show'' (pos-1) fact end
    fun show' 0 second fact = let 
          val fact = @{thm l1} OF [fact]
          in show'' (second-1) fact end
      | show' first second fact = let
          val fact = @{thm l2} OF [fact]
          in show' (first - 1) (second - 1) fact end
    val result = show' first second fact
  in result end
  fun find [] = NONE
    | find (fact::facts) = 
        SOME (show fact) handle TERM _ => find facts
  in find facts end
;;
show_compatibility_fact \<^context> \<^term>\<open>b\<close> \<^term>\<open>d\<close>
\<close>


ML \<open>
fun compatibility_tac ctxt = SUBGOAL (fn (t,i) => (
  case t of
    Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>compatible\<close>,_) $
      (Const(\<^const_name>\<open>pair\<close>,_) $ _ $ _) $ _) =>
        (resolve_tac ctxt [@{thm compatible3}] THEN_ALL_NEW compatibility_tac ctxt) i
(* TODO pair on the right side, chain *)
  | Const(\<^const_name>\<open>Trueprop\<close>,_) $ (Const(\<^const_name>\<open>compatible\<close>,_) $ x $ y) =>
      case show_compatibility_fact ctxt x y of
        SOME thm => solve_tac ctxt [thm] i
      | NONE => no_tac)) 
\<close>

simproc_setup "compatibility" ("compatible x y") = \<open>fn m => fn ctxt => fn ct => let
  val goal = Thm.apply (Thm.apply \<^cterm>\<open>(==) :: bool\<Rightarrow>bool\<Rightarrow>prop\<close> ct) \<^cterm>\<open>True\<close> |> Goal.init
  val goal = SINGLE (resolve_tac ctxt @{thms Eq_TrueI} 1) goal
  val goal = Option.mapPartial (SINGLE (compatibility_tac ctxt 1)) goal
  val thm = Option.map (Goal.finish ctxt) goal
  in thm end\<close>



lemma
  assumes [compatible_lvalues]: "COMPATIBLE (a,b,c,d,e)"
  shows "compatible d b"
  by simp

end
