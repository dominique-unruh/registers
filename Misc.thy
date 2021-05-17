section \<open>Miscellaneous facts\<close>

text \<open>This theory proves various facts that are not directly related to this developments 
but do not occur in the imported theories.\<close>

theory Misc
  imports Bounded_Operators.Bounded_Operators_Code "HOL-Library.Z2"
    Jordan_Normal_Form.Matrix
    "HOL-ex.Sketch_and_Explore"
begin

\<comment> \<open>Remove notation that collides with the notation we use\<close>
no_notation Order.top ("\<top>\<index>")
unbundle no_vec_syntax
unbundle no_inner_syntax

\<comment> \<open>Import notation from Bounded Operator and Jordan Normal Form libraries\<close>
unbundle cblinfun_notation
unbundle jnf_notation

abbreviation "butterket i j \<equiv> butterfly (ket i) (ket j)"
abbreviation "selfbutterket i \<equiv> butterfly (ket i) (ket i)"

term "x::_::onb_enum == y::(_ \<Rightarrow>\<^sub>C\<^sub>L _)"

(* TODO: generalize for any onb instead of ket *)
lemma linfun_cspan: \<open>cspan {butterket i j| (i::'b::finite) (j::'a::finite). True} = UNIV\<close>
proof (rule, simp, rule)
  fix f :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  have frep: \<open>f = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butterket j i))\<close>
  proof (rule cblinfun_ext)
    fix \<phi> :: \<open>'a ell2\<close>
    have \<open>f *\<^sub>V \<phi> = f *\<^sub>V (\<Sum>i\<in>UNIV. butterket i i) *\<^sub>V \<phi>\<close>
      by auto
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. f *\<^sub>V butterket i i *\<^sub>V \<phi>)\<close>
      apply (subst (2) complex_vector.linear_sum)
       apply (simp add: cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. (\<Sum>j\<in>UNIV. butterket j j) *\<^sub>V f *\<^sub>V butterket i i *\<^sub>V \<phi>)\<close>
      by simp
    also have \<open>\<dots> = (\<Sum>i\<in>UNIV. \<Sum>j\<in>UNIV. butterket j j *\<^sub>V f *\<^sub>V butterket i i *\<^sub>V \<phi>)\<close>
      apply (subst (5) complex_vector.linear_sum)
       apply (auto intro!: clinearI simp add: cblinfun_apply_add plus_cblinfun.rep_eq)
      by (metis (no_types, hide_lams) applyOp_scaleC2 plus_cblinfun.rep_eq)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. butterket j j *\<^sub>V f *\<^sub>V butterket i i *\<^sub>V \<phi>)\<close>
      by (simp add: sum.cartesian_product)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butterket j i *\<^sub>V \<phi>))\<close>
      by (simp add: butterfly_def' times_applyOp mult.commute)
    also have \<open>\<dots> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butterket j i)) *\<^sub>V \<phi>\<close>
      unfolding applyOp_scaleC1[symmetric] case_prod_beta
      thm complex_vector.linear_sum
      apply (subst complex_vector.linear_sum[where f=\<open>\<lambda>x. x *\<^sub>V \<phi>\<close>])
       apply (simp add: apply_cblinfun_distr_left clinearI)
      by simp
    finally show \<open>f *\<^sub>V \<phi> = (\<Sum>(i,j)\<in>UNIV. \<langle>ket j, f *\<^sub>V ket i\<rangle> *\<^sub>C (butterket j i)) *\<^sub>V \<phi>\<close>
      by -
  qed
  show \<open>f \<in> cspan {butterket i j |i j. True}\<close>
    apply (subst frep)
    apply (auto simp: case_prod_beta)
    by (metis (mono_tags, lifting) complex_vector.span_base complex_vector.span_scale complex_vector.span_sum mem_Collect_eq)
qed

(* definition bra :: "'a \<Rightarrow> (_,complex) cblinfun" where "bra i = vector_to_cblinfun (ket i)*" for i *)

lemma linfun_cindependent: \<open>cindependent {butterket i j| (i::'b::finite) (j::'a::finite). True}\<close>
proof (rule complex_vector.independent_if_scalars_zero)
  show finite: \<open>finite {butterket (i::'b) (j::'a) |i j. True}\<close>
    apply (subst (6) conj.left_neutral[symmetric])
    apply (rule finite_image_set2)
    by auto
  fix f :: \<open>('a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2) \<Rightarrow> complex\<close> and g :: \<open>'a ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b ell2\<close>
  define lin where \<open>lin = (\<Sum>g\<in>{butterket i j |i j. True}. f g *\<^sub>C g)\<close>
  assume \<open>lin = 0\<close>
  assume \<open>g \<in> {butterket i j |i j. True}\<close>
  then obtain i j where g: \<open>g = butterket i j\<close>
    by auto

  have *: "bra i *\<^sub>V f g *\<^sub>C g *\<^sub>V ket j = 0"
    if \<open>g\<in>{butterket i j |i j. True} - {butterket i j}\<close> for g 
  proof -
    from that
    obtain i' j' where g: \<open>g = butterket i' j'\<close>
      by auto
    from that have \<open>g \<noteq> butterket i j\<close> by auto
    with g consider (i) \<open>i\<noteq>i'\<close> | (j) \<open>j\<noteq>j'\<close>
      by auto
    then show \<open>bra i *\<^sub>V f g *\<^sub>C g *\<^sub>V ket j = 0\<close>
    proof cases
      case i
      then show ?thesis 
        unfolding g by (auto simp: butterfly_def' times_applyOp ket_Kronecker_delta_neq)
    next
      case j
      then show ?thesis
        unfolding g by (auto simp: butterfly_def' times_applyOp ket_Kronecker_delta_neq)
    qed
  qed

  have \<open>0 = bra i *\<^sub>V lin *\<^sub>V ket j\<close>
    using \<open>lin = 0\<close> by auto
  also have \<open>\<dots> = (\<Sum>g\<in>{butterket i j |i j. True}. bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j)\<close>
    unfolding lin_def
    apply (rule complex_vector.linear_sum)
    by (smt (z3) applyOp_scaleC1 applyOp_scaleC2 cblinfun_apply_add clinearI plus_cblinfun.rep_eq)
  also have \<open>\<dots> = (\<Sum>g\<in>{butterket i j}. bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j)\<close>
    apply (rule sum.mono_neutral_right)
    using finite * by auto
  also have \<open>\<dots> = bra i *\<^sub>V (f g *\<^sub>C g) *\<^sub>V ket j\<close>
    by (simp add: g)
  also have \<open>\<dots> = f g\<close>
    unfolding g 
    by (auto simp: butterfly_def' times_applyOp ket_Kronecker_delta_eq)
  finally show \<open>f g = 0\<close>
    by simp
qed

lemma clinear_eq_butterketI:
  fixes F G :: \<open>('a::finite ell2 \<Rightarrow>\<^sub>C\<^sub>L 'b::finite ell2) \<Rightarrow> 'c::complex_vector\<close>
  assumes "clinear F" and "clinear G"
  assumes "\<And>i j. F (butterket i j) = G (butterket i j)"
  shows "F = G"
 apply (rule complex_vector.linear_eq_on_span[where f=F, THEN ext, rotated 3])
     apply (subst linfun_cspan)
  using assms by auto


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

lemma card_bit[simp]: "CARD(bit) = 2"
  using card_2_iff' by force

instantiation bit :: card_UNIV begin
definition "finite_UNIV = Phantom(bit) True"
definition "card_UNIV = Phantom(bit) 2"
instance
  apply intro_classes
  by (simp_all add: finite_UNIV_bit_def card_UNIV_bit_def)
end

lemma sum_single: 
  assumes "finite A"
  assumes "\<And>j. j \<noteq> i \<Longrightarrow> j\<in>A \<Longrightarrow> f j = 0"
  shows "sum f A = (if i\<in>A then f i else 0)"
  apply (subst sum.mono_neutral_cong_right[where S=\<open>A \<inter> {i}\<close> and h=f])
  using assms by auto

lemma mat_of_rows_list_carrier[simp]:
  "mat_of_rows_list n vs \<in> carrier_mat (length vs) n"
  "dim_row (mat_of_rows_list n vs) = length vs"
  "dim_col (mat_of_rows_list n vs) = n"
  unfolding mat_of_rows_list_def by auto


lemma butterfly_times_right: "butterfly \<psi> \<phi> o\<^sub>C\<^sub>L a = butterfly \<psi> (a* *\<^sub>V \<phi>)"
  unfolding butterfly_def'
  by (simp add: cblinfun_apply_assoc vector_to_cblinfun_applyOp)  

lemma butterfly_isProjector:
  \<open>norm x = 1 \<Longrightarrow> isProjector (selfbutter x)\<close>
  by (subst butterfly_proj, simp_all)

lemma apply_idOp[simp]: \<open>(*\<^sub>V) idOp = id\<close>
  by auto

definition "sandwich a b = a o\<^sub>C\<^sub>L b o\<^sub>C\<^sub>L (a*)"

lemma mat_of_cblinfun_sandwich: 
  fixes a :: "(_::onb_enum, _::onb_enum) cblinfun"
  shows \<open>mat_of_cblinfun (sandwich a b) = (let a' = mat_of_cblinfun a in a' * mat_of_cblinfun b * mat_adjoint a')\<close>
  by (simp add: cblinfun_of_mat_timesOp sandwich_def Let_def mat_of_cblinfun_adjoint')

lemma clinear_sandwich[simp]: \<open>clinear (sandwich a)\<close>
  apply (rule clinearI)
  apply (simp add: cblinfun_apply_dist1 cblinfun_apply_dist2 sandwich_def)
  by (simp add: sandwich_def)

lemma sandwich_id: "sandwich idOp = idOp"
  by (metis eq_id_iff idOp.rep_eq idOp_adjoint sandwich_def times_idOp1 times_idOp2)

lemma prod_cases3' [cases type]:
  obtains (fields) a b c where "y = ((a, b), c)"
  by (cases y, case_tac a) blast

lemma lift_cblinfun_comp:
  assumes \<open>a o\<^sub>C\<^sub>L b = c\<close>
  shows \<open>a o\<^sub>C\<^sub>L b = c\<close>
    and \<open>a o\<^sub>C\<^sub>L (b o\<^sub>C\<^sub>L d) = c o\<^sub>C\<^sub>L d\<close>
    and \<open>a *\<^sub>S (b *\<^sub>S S) = c *\<^sub>S S\<close>
    and \<open>a *\<^sub>V (b *\<^sub>V x) = c *\<^sub>V x\<close>
  apply (fact assms)
  apply (metis assms cblinfun_apply_assoc)
  using assms assoc_left(2) apply blast
  by (metis assms times_applyOp)



(* Abbreviations: "mutually f (x1,x2,x3,\<dots>)" expands to a conjunction
   of all "f xi xj" with i\<noteq>y.

   "each f (x1,x2,x3,\<dots>)" expands to a conjunction of all "f xi". *)

syntax "_mutually" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("mutually _ '(_')")
syntax "_mutually2" :: "'a \<Rightarrow> 'b \<Rightarrow> args \<Rightarrow> args \<Rightarrow> 'c"

translations "mutually f (x)" => "CONST True"
translations "mutually f (_args x y)" => "f x y \<and> f y x"
translations "mutually f (_args x (_args x' xs))" => "_mutually2 f x (_args x' xs) (_args x' xs)"
translations "_mutually2 f x y zs" => "f x y \<and> f y x \<and> _mutually f zs"
translations "_mutually2 f x (_args y ys) zs" => "f x y \<and> f y x \<and> _mutually2 f x ys zs"

syntax "_each" :: "'a \<Rightarrow> args \<Rightarrow> 'b" ("each _ '(_')")
translations "each f (x)" => "f x"
translations "_each f (_args x xs)" => "f x \<and> _each f xs"


lemma enum_inj:
  assumes "i < CARD('a)" and "j < CARD('a)"
  shows "(Enum.enum ! i :: 'a::enum) = Enum.enum ! j \<longleftrightarrow> i = j"
  using inj_on_nth[OF enum_distinct, where I=\<open>{..<CARD('a)}\<close>]
  using assms by (auto dest: inj_onD simp flip: card_UNIV_length_enum)


lemma [simp]: "dim_col (mat_adjoint m) = dim_row m"
  unfolding mat_adjoint_def by simp
lemma [simp]: "dim_row (mat_adjoint m) = dim_col m"
  unfolding mat_adjoint_def by simp

end
