theory Misc
  imports Bounded_Operators.Complex_L2 "HOL-Library.Z2"
begin

unbundle cblinfun_notation

(* TODO should be in bounded operators (non-finite case). Implicitly proven in: *)
thm equal_basis_0
thm equal_ket
thm superposition_principle_linear_ket
lemma cbounded_linear_equal_ket:
  fixes f g :: \<open>'a::finite ell2 \<Rightarrow> _\<close>
  assumes \<open>clinear f\<close>
  assumes \<open>clinear g\<close>
  assumes \<open>\<And>i. f (ket i) = g (ket i)\<close>
  shows \<open>f = g\<close>
  apply (rule ext)
  apply (rule complex_vector.linear_eq_on_span[where f=f and g=g and B=\<open>range ket\<close>])
  using assms apply auto
  by (metis ket_ell2_span span_finite_dim finite_class.finite_UNIV finite_imageI iso_tuple_UNIV_I) 

lemma cbounded_linear_finite_ell2[simp, intro!]:
  fixes f :: \<open>'a::finite ell2 \<Rightarrow> 'b::complex_normed_vector\<close>
  assumes "clinear f"
  shows \<open>cbounded_linear f\<close>
  apply (subst cblinfun_operator_finite_dim[where basis=\<open>ket ` UNIV\<close>])
  using assms apply (auto intro!: cindependent_ket)
  by (metis finite_class.finite_UNIV finite_imageI iso_tuple_UNIV_I ket_ell2_span span_finite_dim)


(* TODO belongs into bounded operators *)
lemma apply_cblinfun_distr_left: "(A + B) *\<^sub>V x = A *\<^sub>V x + B *\<^sub>V x"
  apply transfer by simp

lemma ket_Kronecker_delta: \<open>\<langle>ket i, ket j\<rangle> = (if i=j then 1 else 0)\<close>
  by (simp add: ket_Kronecker_delta_eq ket_Kronecker_delta_neq)


definition \<open>butter i j = vector_to_cblinfun (ket i) o\<^sub>C\<^sub>L (vector_to_cblinfun (ket j) :: complex \<Rightarrow>\<^sub>C\<^sub>L _)*\<close>

lemma sum_butter[simp]: \<open>(\<Sum>(i::'a::finite)\<in>UNIV. butter i i) = idOp\<close>
  apply (rule equal_ket)
  apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>y. y *\<^sub>V ket _\<close>])
  apply (auto simp add: apply_cblinfun_distr_left clinearI butter_def times_applyOp ket_Kronecker_delta)
  apply (subst sum.mono_neutral_cong_right[where S=\<open>{_}\<close>])
  by auto

lemma linfun_cspan: \<open>cspan {butter i j| (i::'b::finite) (j::'a::finite). True} = UNIV\<close>
proof (rule, simp, rule)
  fix f :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  have frep: \<open>f = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i))\<close>
  proof (rule cblinfun_ext)
    fix \<phi> :: \<open>'a ell2\<close>
    have \<open>f *\<^sub>V \<phi> = f *\<^sub>V (\<Sum>i\<in>UNIV. butter i i) *\<^sub>V \<phi>\<close>
      by auto
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      apply (subst (2) complex_vector.linear_sum)
       apply (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. butter j j) *\<^sub>V f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. butter j j *\<^sub>V f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      apply (subst (3) complex_vector.linear_sum)
       apply (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
      by simp
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. butter j j *\<^sub>V f *\<^sub>V butter i i *\<^sub>V \<phi>)\<close>
      by (simp add: sum.cartesian_product)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i *\<^sub>V \<phi>))\<close>
      by (simp add: butter_def times_applyOp mult.commute)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i)) *\<^sub>V \<phi>\<close>
      unfolding applyOp_scaleC1[symmetric] case_prod_beta
      thm complex_vector.linear_sum
      apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>x. x *\<^sub>V \<phi>\<close>])
       apply (simp add: apply_cblinfun_distr_left clinearI)
      by simp
    finally show \<open>f *\<^sub>V \<phi> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butter j i)) *\<^sub>V \<phi>\<close>
      by -
  qed
  show \<open>f \<in> cspan {butter i j |i j. True}\<close>
    apply (subst frep)
    apply (auto simp: case_prod_beta)
    by (metis (mono_tags, lifting) complex_vector.span_base complex_vector.span_scale complex_vector.span_sum mem_Collect_eq)
qed

definition bra :: "'a \<Rightarrow> (_,complex) cblinfun" where "bra i = vector_to_cblinfun (ket i)*" for i

lemma linfun_cindependent: \<open>cindependent {butter i j| (i::'b::finite) (j::'a::finite). True}\<close>
proof (rule independent_if_scalars_zero)
  show finite: \<open>finite {butter (i::'b) (j::'a) |i j. True}\<close>
    apply (subst (6) conj.left_neutral[symmetric])
    apply (rule finite_image_set2)
    by auto
  fix f :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> complex\<close> and g :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  define lin where \<open>lin = (\<Sum>g\<in>{butter i j |i j. True}. f g *\<^sub>C g)\<close>
  assume \<open>lin = 0\<close>
  assume \<open>g \<in> {butter i j |i j. True}\<close>
  then obtain i j where g: \<open>g = butter i j\<close>
    by auto
  (* define bra :: "'b \<Rightarrow> (_,complex) cblinfun" where "bra i = vector_to_cblinfun (ket i)*" for i *)

  have *: "bra i *\<^sub>V f g *\<^sub>C g *\<^sub>V ket j = 0"
    if \<open>g\<in>{butter i j |i j. True} - {butter i j}\<close> for g 
  proof -
    from that
    obtain i' j' where g: \<open>g = butter i' j'\<close>
      by auto
    from that have \<open>g \<noteq> butter i j\<close> by auto
    with g consider (i) \<open>i\<noteq>i'\<close> | (j) \<open>j\<noteq>j'\<close>
      by auto
    then show \<open>bra i *\<^sub>V f g *\<^sub>C g *\<^sub>V ket j = 0\<close>
    proof cases
      case i
      then show ?thesis 
        unfolding g by (auto simp: butter_def times_applyOp bra_def ket_Kronecker_delta_neq)
    next
      case j
      then show ?thesis
        unfolding g by (auto simp: butter_def times_applyOp ket_Kronecker_delta_neq)
    qed
  qed

  have \<open>0 = bra i *\<^sub>V lin *\<^sub>V ket j\<close>
    using \<open>lin = 0\<close> by auto
  also have \<open>\<dots> = (\<Sum>g\<in>{butter i j |i j. True}. bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j)\<close>
    unfolding lin_def
    apply (rule complex_vector.linear_sum)
    by (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
  also have \<open>\<dots> = (\<Sum>g\<in>{butter i j}. bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j)\<close>
    apply (rule sum.mono_neutral_right)
    using finite * by auto
  also have \<open>\<dots> = bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j\<close>
    by (simp add: g)
  also have \<open>\<dots> = f g\<close>
    unfolding g 
    by (auto simp: butter_def times_applyOp bra_def ket_Kronecker_delta_eq)
  finally show \<open>f g = 0\<close>
    by simp
qed

(* Declares the ML antiquotation @{fact ...}. In ML code,
  @{fact f} for a theorem/fact name f is replaced by an ML string
  containing a printable(!) representation of fact. (I.e.,
  if you print that string using writeln, the user can ctrl-click on it.)
 *)
setup \<open>ML_Antiquotation.inline_embedded \<^binding>\<open>fact\<close>
((Args.context -- Scan.lift Args.name_position) >> (fn (ctxt,namepos) => let
  val facts = Proof_Context.facts_of ctxt
  val fullname = Facts.check (Context.Proof ctxt) facts namepos
  val (markup, shortname) = Proof_Context.markup_extern_fact ctxt fullname
  val string = Markup.markups markup shortname
  in ML_Syntax.print_string string end
))
\<close>


instantiation bit :: enum begin
definition "enum_bit = [0::bit,1]"
definition "enum_all_bit P \<longleftrightarrow> P (0::bit) \<and> P 1"
definition "enum_ex_bit P \<longleftrightarrow> P (0::bit) \<or> P 1"
instance
  apply intro_classes
  apply (auto simp: enum_bit_def enum_all_bit_def enum_ex_bit_def)
  by (metis bit_not_one_imp)+
end


end
