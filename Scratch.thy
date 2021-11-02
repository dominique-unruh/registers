theory Scratch
  imports Classical_Extra
    "HOL-Types_To_Sets.Types_To_Sets"
begin

class domain = fixes domain_x :: 'a and domain_y assumes \<open>domain_x = domain_y\<close>

axiomatization where complement_unique: \<open>compatible F G \<Longrightarrow> iso_register (F;G) \<Longrightarrow> compatible F H \<Longrightarrow> iso_register (F;H)
          \<Longrightarrow> equivalent_registers G H\<close> 
    for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close> and G :: \<open>'g::domain update \<Rightarrow> 'b update\<close> and H :: \<open>'h::domain update \<Rightarrow> 'b update\<close>

definition \<open>complements F G \<longleftrightarrow> compatible F G \<and> iso_register (F;G)\<close>
  for F G :: \<open>_::domain update \<Rightarrow> 'b::domain update\<close>

type_synonym ('a, 'b) complement_domain2 = \<open>'b set\<close>

inductive_set equivalent_memories :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> ('b*'b) set\<close> for F where
  equivalent_memories: \<open>setter F a m1 = m2 \<Longrightarrow> (m1,m2) \<in> equivalent_memories F\<close>

definition U :: \<open>('a::domain update \<Rightarrow> 'b::domain update) \<Rightarrow> ('a, 'b) complement_domain2 set\<close> where
  \<open>U F = UNIV // equivalent_memories F\<close>

lemma equiv_equivalent_memories: \<open>equiv UNIV (equivalent_memories F)\<close> if \<open>register F\<close>
proof (intro equivI refl_onI symI transI)
  show \<open>equivalent_memories F \<subseteq> UNIV \<times> UNIV\<close>
    by auto
  fix x y z
  show \<open>(x, x) \<in> equivalent_memories F\<close>
    apply (rule equivalent_memories.intros[where a=\<open>getter F x\<close>])
    by (metis that valid_getter_setter_def valid_getter_setter_getter_setter)
  show \<open>(x, y) \<in> equivalent_memories F\<close> if \<open>(y, x) \<in> equivalent_memories F\<close>
    using that apply cases 
    apply (rule equivalent_memories.intros[where a=\<open>getter F y\<close>])
    by (smt (verit, ccfv_SIG) \<open>register F\<close> valid_getter_setter_def valid_getter_setter_getter_setter)
  show \<open>(x, z) \<in> equivalent_memories F\<close> 
    if \<open>(x, y) \<in> equivalent_memories F\<close> and \<open>(y, z) \<in> equivalent_memories F\<close>
    using that(1) apply cases 
    using that(2) apply cases 
    apply (rule equivalent_memories.intros[where a=\<open>getter F z\<close>])
    by (smt (verit, best) \<open>register F\<close> valid_getter_setter_def valid_getter_setter_getter_setter)
qed

lemma U_inhab: \<open>register F \<Longrightarrow> U F \<noteq> {}\<close>
  unfolding U_def by force

lemma setter_determines_register:
  assumes \<open>register F\<close> \<open>register G\<close>
  assumes eq: \<open>\<And>a m. setter F a m = setter G a m\<close>
  shows \<open>F = G\<close>
proof -
  have \<open>valid_getter_setter (getter F) (setter F)\<close> \<open>valid_getter_setter (getter G) (setter G)\<close>
    by (simp_all add: assms)
  with eq have \<open>getter F = getter G\<close>
    unfolding valid_getter_setter_def
    apply (auto intro!: ext) by metis
  moreover have \<open>F = register_from_getter_setter (getter F) (setter F)\<close>
    by (simp add: assms(1))
  moreover have \<open>G = register_from_getter_setter (getter G) (setter G)\<close>
    by (simp add: assms(2))
  ultimately show \<open>F = G\<close>
    using eq[abs_def] by auto
qed

lemma setter_id[simp]: \<open>setter id a m = a\<close>
  unfolding setter_def register_apply_def by auto

lemma setter_chain:
  assumes \<open>register F\<close> and \<open>register G\<close>
  shows \<open>setter (F o G) a m = setter F (setter G a (getter F m)) m\<close>
  apply (auto simp: setter_def register_apply_def o_def)
  by (smt (verit, best) assms(1) assms(2) getter_of_register_from_getter_setter option.expand option.sel option.simps(3) register_def register_from_getter_setter_def register_total total_fun_def)

lemma setter_surj_iso_reg:
  fixes F :: \<open>'a update \<Rightarrow> 'b update\<close>
  assumes \<open>register F\<close>
  assumes \<open>surj (\<lambda>a. setter F a m0)\<close>
  shows \<open>iso_register F\<close>
proof -
  define s where \<open>s a = setter F a m0\<close> for a
  then have \<open>inj s\<close>
    by (metis assms(1) inj_def valid_getter_setter_def valid_getter_setter_getter_setter)
  then have [simp]: \<open>bij s\<close>
    by (simp add: s_def assms(2) bijI)

  have s: \<open>s a = setter F a m\<close> for a m
    by (smt (verit, ccfv_threshold) \<open>bij s\<close> \<open>s \<equiv> \<lambda>a. setter F a m0\<close> assms(1) bij_pointE valid_getter_setter_def valid_getter_setter_getter_setter)

  define F1 where \<open>F1 = permutation_register s\<close>
  then have \<open>register F1\<close>
    using \<open>bij s\<close> permutation_register_register by blast
  have \<open>setter (F1 o F) a m = setter id a m\<close> for a m
  proof -
    have \<open>setter (F1 o F) a m = setter F1 (setter F a (getter F1 m)) m\<close>
      using \<open>register F1\<close> \<open>register F\<close> by (rule setter_chain)
    also have \<open>\<dots> = setter F1 (s a) m\<close>
      unfolding s[symmetric] by simp
    also have \<open>\<dots> = inv s (s a)\<close>
      by (simp add: F1_def setter_permutation_register)
    also have \<open>\<dots> = a\<close>
      by (simp add: \<open>inj s\<close>)
    also have \<open>\<dots> = setter id a m\<close>
      by auto
    finally show ?thesis
      by -
  qed
  then have \<open>F1 o F = id\<close>
    apply (rule setter_determines_register[rotated 2])
    apply (simp add: \<open>register F1\<close> assms(1))
    by auto
  have \<open>setter (F o F1) a m = setter id a m\<close> for a m
  proof -
    have \<open>setter (F o F1) a m = setter F (setter F1 a (getter F m)) m\<close>
      using \<open>register F\<close> \<open>register F1\<close> by (rule setter_chain)
    also have \<open>\<dots> = s (setter F1 a (getter F m))\<close>
      by  (simp add: s[symmetric])
    also have \<open>\<dots> = s (inv s a)\<close>
      by (simp add: F1_def setter_permutation_register)
    also have \<open>\<dots> = a\<close>
      by (meson \<open>bij s\<close> bij_inv_eq_iff)
    also have \<open>\<dots> = setter id a m\<close>
      by auto
    finally show ?thesis
      by -
  qed
  then have \<open>F o F1 = id\<close>
    apply (rule setter_determines_register[rotated 2])
    apply (simp add: \<open>register F1\<close> assms(1))
    by auto
  show ?thesis
    using \<open>F \<circ> F1 = id\<close> \<open>F1 \<circ> F = id\<close> \<open>register F1\<close> assms(1) iso_register_def by blast
qed

lemma getter_inj_iso_reg:
  assumes \<open>register F\<close>
  assumes \<open>inj (getter F)\<close>
  shows \<open>iso_register F\<close>
proof -
  fix m0
  define s where \<open>s a = setter F a m0\<close> for a
  have \<open>getter F (s a) = a\<close> for a
    by (metis assms(1) s_def valid_getter_setter_def valid_getter_setter_getter_setter)
  with \<open>inj (getter F)\<close>
  have \<open>surj s\<close>
    by (metis inv_f_f surjI)
  with \<open>register F\<close> show \<open>iso_register F\<close>
    unfolding s_def 
    by (rule setter_surj_iso_reg)
qed

lemma pair_valid:
  assumes \<open>compatible F G\<close>
  shows \<open>valid_getter_setter (\<lambda>m. (getter F m, getter G m)) (\<lambda>(a, b) m. setter F a (setter G b m))\<close>
  apply (simp add: valid_getter_setter_def)
  using assms apply auto
  apply (metis compatible_register1 compatible_register2 valid_getter_setter_def valid_getter_setter_getter_setter)
  apply (meson compatible_register1 valid_getter_setter_def valid_getter_setter_getter_setter)
  apply (smt (verit, del_insts) Axioms_Classical.compatible_setter comp_apply compatible_def valid_getter_setter_def valid_getter_setter_getter_setter)
  by (smt (verit, del_insts) Classical_Extra.compatible_setter comp_eq_dest_lhs compatible_register1 compatible_register2 valid_getter_setter_def valid_getter_setter_getter_setter)

lemma getter_register_pair[simp]:
  assumes "compatible F G"
  shows \<open>getter (F;G) = (\<lambda>m. (getter F m, getter G m))\<close>
  unfolding register_pair_def
  apply (subst getter_of_register_from_getter_setter)
  using assms apply (rule pair_valid)
  by simp

lemma trans'':
  fixes F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>
  assumes \<open>register F\<close>
  shows
  \<open>\<forall>(Rep :: 'd::domain \<Rightarrow> ('a,'b) complement_domain2) Abs.
  type_definition Rep Abs (U F) \<longrightarrow>
  (\<exists>G :: 'd update \<Rightarrow> 'b update. complements F G)\<close>
proof (intro allI impI)
  fix Rep :: \<open>'d::domain \<Rightarrow> ('a,'b) complement_domain2\<close> and Abs
  assume "typedef": \<open>type_definition Rep Abs (U F)\<close>
  have Abs_inverse: \<open>y \<in> U F \<Longrightarrow> Rep (Abs y) = y\<close> for y
    by (meson "typedef" type_definition.Abs_inverse)
  have Rep_inverse[simp]: \<open>Abs (Rep x) = x\<close> for x
    by (meson "typedef" type_definition.Rep_inverse)

  define g where \<open>g m = Abs (equivalent_memories F `` {m})\<close> for m :: 'b
  define repr where \<open>repr m = (SOME m'. m' \<in> Rep m)\<close> for m :: 'd
  define s where \<open>s x m = setter F (getter F m) (repr x)\<close> for x m
  define G :: \<open>'d update \<Rightarrow> 'b update\<close> where \<open>G = register_from_getter_setter g s\<close>

  have [simp]: \<open>setter F (getter F b) b = b\<close> for b
    by (metis assms valid_getter_setter_def valid_getter_setter_getter_setter)
  have Rep_quotient[simp]: \<open>Rep a \<in> UNIV // equivalent_memories F\<close> for a
    by (metis "typedef" U_def type_definition.Rep)
  have repr_Rep[simp]: \<open>repr a \<in> Rep a\<close> for a
    unfolding repr_def
    apply (rule someI_ex)
    using Rep_quotient assms equiv_Eps_in equiv_equivalent_memories by blast
  have repr_in: \<open>(repr (g b), b) \<in> equivalent_memories F\<close> for b
    unfolding repr_def g_def
    apply (subst Abs_inverse)
     apply (simp add: U_def quotientI)
    by (metis Image_singleton_iff assms equiv_class_subset equiv_equivalent_memories iso_tuple_UNIV_I someI_ex subsetI subset_equiv_class)

  have sg: \<open>b = s (g b) b\<close> for b
  proof -
    from repr_in[of b]
    obtain a where [simp]: \<open>setter F a (repr (g b)) = b\<close>
      apply cases
      apply atomize_elim
      by auto
    have \<open>s (g b) b = setter F (getter F b) (repr (g b))\<close>
      by (simp add: s_def)
    also have \<open>\<dots> = setter F (getter F b) (setter F a (repr (g b)))\<close>
      by (metis assms valid_getter_setter_def valid_getter_setter_getter_setter)
    also have \<open>\<dots> = setter F (getter F b) b\<close>
      by simp
    also have \<open>\<dots> = b\<close>
      by simp
    finally show ?thesis
      by (simp add: s_def)
  qed
  moreover have gs: \<open>g (s a b) = a\<close> for a b
  proof -
    obtain a' where Rep_a: \<open>Rep a = equivalent_memories F `` {a'}\<close>
      by (meson Rep_quotient quotientE)
    have *: \<open>(setter F (getter F b) (repr a), repr a) \<in> equivalent_memories F\<close>
      by (smt (verit, best) assms equivalent_memories.equivalent_memories register_def setter_of_register_from_getter_setter valid_getter_setter_def)
    
    have \<open>Rep (g (s a b)) = equivalent_memories F `` {setter F (getter F b) (repr a)}\<close>
      by (simp add: Abs_inverse U_def \<open>g \<equiv> \<lambda>m. Abs (equivalent_memories F `` {m})\<close> quotientI s_def)
    also have \<open>\<dots> = equivalent_memories F `` {repr a}\<close>
      apply (rule equiv_class_eq)
      using assms apply (rule equiv_equivalent_memories)
      using * by fastforce
    also have \<open>\<dots> = Rep a\<close>
      apply (subst Rep_a)
      apply (rule equiv_class_eq)
      using assms apply (rule equiv_equivalent_memories)
      by (metis Image_singleton_iff Rep_a repr_Rep assms equiv_class_subset equiv_equivalent_memories iso_tuple_UNIV_I subset_equiv_class)
    finally show ?thesis
      by (metis Rep_inverse)
  qed
  moreover have \<open>s a (s a' b) = s a b\<close> for a a' b
  proof -
    have \<open>(s a (s a' b), s a b) \<in> equivalent_memories F\<close>
      by (smt (z3) assms equiv_class_eq_iff equiv_equivalent_memories equivalent_memories.equivalent_memories s_def)
    then obtain b' where \<open>setter F b' (s a (s a' b)) = s a b\<close>
      by (meson equivalent_memories.cases)
    then have b'_def: \<open>b' = getter F b\<close>
      by (metis assms s_def valid_getter_setter_def valid_getter_setter_getter_setter)
    have \<open>getter F (s a (s a' b)) = b'\<close>
      unfolding s_def b'_def
      by (metis (no_types, hide_lams) assms valid_getter_setter_def valid_getter_setter_getter_setter)
    show ?thesis
      using \<open>getter F (s a (s a' b)) = b'\<close> \<open>setter F b' (s a (s a' b)) = s a b\<close> by force
  qed
  ultimately have [simp]: \<open>valid_getter_setter g s\<close>
    unfolding valid_getter_setter_def by auto
  then have [simp]: \<open>register G\<close>
    unfolding G_def by simp
  have [simp]: \<open>getter G = g\<close>
    by (simp add: G_def \<open>valid_getter_setter g s\<close>)

  have commute: \<open>setter F x (s y m) = s y (setter F x m)\<close> for x y m
    by (smt (verit, best) s_def assms valid_getter_setter_def valid_getter_setter_getter_setter)

  have [simp]: \<open>compatible F G\<close>
    unfolding G_def 
    apply (subst register_from_getter_setter_of_getter_setter[symmetric])
     apply (fact \<open>register F\<close>)
    apply (rule register_from_getter_setter_compatibleI)
    apply (simp add: assms)
    apply (simp add: \<open>valid_getter_setter g s\<close>)
    by (simp add: commute)

  define P where \<open>P = (F;G)\<close>
  have [simp]: \<open>register P\<close>
    using P_def \<open>compatible F G\<close> pair_is_register by blast

  define pinv where \<open>pinv = (\<lambda>(f,g). setter F f (repr g))\<close>
  have \<open>pinv (getter P m) = m\<close> for m
    unfolding pinv_def P_def
    apply (subst getter_register_pair)
    using s_def sg by auto
  then have [simp]: \<open>iso_register P\<close>
    apply (auto intro!: getter_inj_iso_reg)
    by (metis injI)

  have \<open>complements F G\<close>
    using P_def \<open>compatible F G\<close> \<open>iso_register P\<close> complements_def by blast
  
  then show \<open>\<exists>G :: 'd update \<Rightarrow> 'b update. complements F G\<close>
    by auto
qed

lemma aux: \<open>(\<forall>x y. P x y \<longrightarrow> Q) \<Longrightarrow> (\<exists>x y. P x y) \<Longrightarrow> Q\<close> for P :: \<open>'x \<Rightarrow> 'y \<Rightarrow> bool\<close> and Q
    by auto

lemma class_U: \<open>type_definition x y (U F) \<Longrightarrow> class.domain (undefined x) (undefined x)\<close>
  for x :: \<open>'g \<Rightarrow> ('a::domain, 'b::domain) complement_domain2\<close> and y
  unfolding class.domain_def
  by auto

lemma class_U': \<open>(\<exists>x y. type_definition x y (U F)) \<Longrightarrow> class.domain undefined undefined\<close>
  for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>
  sorry

(* lemma l1'': \<open>(\<exists>G::'g::domain update \<Rightarrow> 'b::domain update. complements F G) \<Longrightarrow> undefined F\<close>
  for F :: \<open>'a::domain update \<Rightarrow> 'b::domain update\<close>
  using l1 by blast *)

(* lemma aux2: \<open>(\<And>G :: 'a::domain update \<Rightarrow> _. complements F G \<Longrightarrow> P) \<Longrightarrow> (\<exists>G :: 'a update \<Rightarrow> _. complements F G \<Longrightarrow> P)\<close>
  by metis *)

ML \<open>
fun dest_updateT (Type("fun", [T, Type(\<^type_name>\<open>option\<close>, [T'])])) = 
      if T=T' then T
      else raise TYPE ("dest_updateT", [T,T'], [])
  | dest_updateT T = raise TYPE ("dest_updateT", [T], [])
\<close>



lemma aux4: \<open>(\<exists>G :: 'a::domain update \<Rightarrow> _. complements F G) \<Longrightarrow> (complements F (SOME G :: 'a update \<Rightarrow> _. complements F G))\<close>
  apply (rule someI_ex[where P=\<open>\<lambda>G. complements F G\<close>])
  by simp


(* An example lemma from which we want to remove the "complements F G" assumption *)
lemma l1:
  fixes  F :: \<open>'a::{domain,finite} update \<Rightarrow> 'b::domain update\<close>
  fixes  G :: \<open>'g::domain update \<Rightarrow> 'b update\<close>
  assumes \<open>complements (bla F :: 'c::{domain} update \<Rightarrow> _) G\<close>
  assumes \<open>True\<close>
  shows "undefined F"
  sorry

(* declare [[show_sorts]] *)
declare [[eta_contract=false]]

ML \<open>
(* th must be of the form \<open>complements F ?G \<Longrightarrow> P\<close> where ?G :: ?'g::domain \<Rightarrow> U update is a schematic variable,
   and ?'g does not occur in F::T update \<Rightarrow> U update or P. 

   remove_complement_assumption ctxt th returns \<open>register F \<Longrightarrow> P\<close>, with potential duplicated premises removed. *)
fun remove_complement_assumption ctxt th = let
  (* reg = F, compl = ?G *)
  val (reg,compl,_) = case Thm.prop_of th of
    Const(\<^const_name>\<open>Pure.imp\<close>,_) $ (Const(\<^const_name>\<open>Trueprop\<close>,_) $
         (Const(\<^const_name>\<open>complements\<close>,_) $ reg $ compl)) $ lemma => (reg,compl,lemma)
        | _ => raise TERM ("remove_complement_assumption: wrong shape of theorem", [Thm.prop_of th])
  (* compl_typ = type of ?G *)
  val (_, compl_typ) = case compl of Var n => n
        | _ => raise TERM ("remove_complement_assumption: complement not a variable", [Thm.prop_of th, compl])
  (* compl_in_typ = ?'g *)
  val compl_in_typ = compl_typ |> dest_funT |> fst |> dest_updateT
  (* compl_in_typ_idxname = ("g",0) or whatever the name of ?'g. 
     compl_in_typ_sort = sort of ?'g *)
  val (compl_in_typ_idxname, compl_in_typ_sort) = case compl_in_typ of TVar v => v
        | _ => raise TERM ("remove_complement_assumption: complement domain-type not a type variable", [Thm.prop_of th, compl])
  val _ = if compl_in_typ_sort = \<^sort>\<open>domain\<close> then () else 
            raise TYPE ("remove_complement_assumption: complement domain-type does not have sort domain", [compl_in_typ], [Thm.prop_of th, compl])
  (* reg_typ = type of F *)
  val reg_typ = fastype_of reg
  (* reg_in_typ = T *)
  val reg_in_typ = reg_typ |> dest_funT |> fst |> dest_updateT
  (* reg_out_typ = U *)
  val reg_out_typ = reg_typ |> dest_funT |> snd |> dest_updateT
  (* th = (\<exists>G::compl_typ. complements F G) \<Longrightarrow> P *)
  (* Here (and in the following, F is not necessarily eta-contracted even if it was before) *)
  val th = @{thm aux4} RS th
  (* TODO *)
  val l2 = @{thm trans''[unoverload_type ?'d, THEN aux]}
  (* th = DOMAIN \<Longrightarrow> (\<exists>G::?'g::type update \<Rightarrow> U update. complements F G) \<Longrightarrow> P.
     (Note the changed sort of ?'g)
     Here DOMAIN is something like "class.domain ..." where ... are fresh schematic variables *)
  val th = Unoverload_Type.unoverload_type (Context.Proof ctxt) [compl_in_typ_idxname] th
  (* reg_ct = F (as cterm) *)
  val reg_ct = Thm.cterm_of ctxt reg
  (* th = DOMAIN \<Longrightarrow> register F \<Longrightarrow> TYPEDEF \<Longrightarrow> P
     Here TYPEDEF = \<exists>(x :: ?'g::type => _) y. type_definition x y (U F) *)
  val th = l2 RSN (2, th)
  (* classU = TYPEDEF \<Longrightarrow> DOMAIN *)
  val classU = @{thm class_U'} 
      |> Thm.instantiate ([((("'a",0),\<^sort>\<open>domain\<close>), Thm.ctyp_of ctxt reg_in_typ), 
        ((("'b",0),\<^sort>\<open>domain\<close>), Thm.ctyp_of ctxt reg_out_typ),
        ((("'c",0),\<^sort>\<open>type\<close>), Thm.ctyp_of ctxt (TVar (compl_in_typ_idxname, \<^sort>\<open>type\<close>)))],
       [((("F",0), reg_typ), reg_ct)])
  (* th = TYPEDEF \<Longrightarrow> DOMAIN \<Longrightarrow> register F \<Longrightarrow> TYPEDEF \<Longrightarrow> P *)
  val th = Thm.bicompose (SOME ctxt) {flatten=false, incremented=false, match=false} (false,classU,1) 1 th |> Seq.hd
  (* th = TYPEDEF \<Longrightarrow> TYPEDEF \<Longrightarrow> register F \<Longrightarrow> TYPEDEF \<Longrightarrow> P *)
  val th = Thm.bicompose (SOME ctxt) {flatten=false, incremented=false, match=false} (false,classU,1) 2 th |> Seq.hd
  (* th = TYPEDEF \<Longrightarrow> TYPEDEF \<Longrightarrow> TYPEDEF \<Longrightarrow> register F \<Longrightarrow> P *)
  val th = Drule.rearrange_prems [3] th
  (* As before, but eta-reduced (so that all "TYPEDEF" are equal, not just eta-equivalent) *)
  val th = Conv.fconv_rule Thm.eta_conversion th
  (* th = TYPEDEF \<Longrightarrow> register F \<Longrightarrow> P  (and possibly some duplicate subgoal removed in P) *)
  val th = distinct_subgoals_tac th |> Seq.hd
  (* th = U F \<noteq> {} \<Longrightarrow> register F \<Longrightarrow> P *)
  val th = Local_Typedef.cancel_type_definition th
  (* th = register F \<Longrightarrow> register F \<Longrightarrow> P (F is not necessarily eta-contracted even if it was before) *)
  val th = @{thm U_inhab} RS th
  (* As before, but eta-contracted *)
  val th = Conv.fconv_rule Thm.eta_conversion th
  (* th = register F \<Longrightarrow> P *)
  val th = distinct_subgoals_tac th |> Seq.hd
in
  th
end
;;
  remove_complement_assumption \<^context> @{thm l1}
\<close>


ML \<open>
val remove_complement_assumption_attr = Thm.rule_attribute [] 
    (fn context => remove_complement_assumption (Context.proof_of context))
val _ = Context.>> (Context.map_theory (Attrib.setup \<^binding>\<open>remove_complement_assumption\<close>
  (Scan.lift (Scan.succeed remove_complement_assumption_attr))
    "TODO comment"))
\<close>

thm l1[remove_complement_assumption]

end
