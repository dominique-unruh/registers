theory Tensor_LValues
  imports LValues_Typed Complex_Main
"HOL-ex.Sketch_and_Explore"
begin


section Matrices

(* TODO: make non-square *)
typedef 'a matrix = "UNIV::('a\<Rightarrow>'a\<Rightarrow>complex) set" by simp
setup_lifting type_definition_matrix

lift_definition tensor :: "'a matrix \<Rightarrow> 'b matrix \<Rightarrow> ('a*'b) matrix" is
  "%A B. \<lambda>(r1,r2) (c1,c2). A r1 c1 * B r2 c2" .

(* TODO associator *)
(* TODO swapper *)

instantiation matrix :: (type) ab_group_add begin
lift_definition plus_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i j. A i j + B i j".
lift_definition minus_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i j. A i j - B i j".
lift_definition uminus_matrix :: "'a matrix \<Rightarrow> 'a matrix" is "%A i j. - A i j".
lift_definition zero_matrix :: "'a matrix" is "\<lambda>i j. 0".
instance sorry
end


instantiation matrix :: (type) "one" begin
lift_definition one_matrix :: "'a matrix" is "\<lambda>i j. if i=j then 1 else 0".
instance apply intro_classes.
end

instantiation matrix :: (finite) "times" begin
lift_definition times_matrix :: "'a matrix \<Rightarrow> 'a matrix \<Rightarrow> 'a matrix" is "%A B i k. (\<Sum>j\<in>UNIV. A i j * B j k)".
instance apply intro_classes.
end

instantiation matrix :: (finite) ring_1 begin
instance apply intro_classes sorry
end

abbreviation "delta x y == (if x=y then 1 else 0)"

lift_definition matrix_on :: "'b matrix \<Rightarrow> ('a,'b) lvalue \<Rightarrow> 'a matrix" is
  "\<lambda>B x (r::'a) (c::'a). B (fst (split_memory x r)) (fst (split_memory x c))
  * delta (snd (split_memory x r)) (snd (split_memory x c))" .

lemma matrix_on_lift_left:
  assumes compat[simp]: "compatible_lvalues x y"
  defines "xy == lvalue_pair x y"
  shows "matrix_on A x = matrix_on (tensor A 1) xy"
proof (transfer fixing: x y xy, rule ext, rule ext)
  fix A :: "'b \<Rightarrow> 'b \<Rightarrow> complex" and r c

  define xrest yrest xyrest
    where "xrest m = snd (split_memory x m)" 
      and "yrest m = snd (split_memory y m)"
      and "xyrest m = snd (split_memory xy m)" for m

  have [simp]: "valid_lvalue xy"
    unfolding xy_def by simp
  have [simp]: "valid_lvalue x"
    using LValues_Typed.compatible_valid1 compat by blast
  have [simp]: "valid_lvalue y"
    using LValues_Typed.compatible_valid2 compat by blast

  have [simp]: "fst (split_memory x r) = getter x r" for r
    by simp
  have [simp]: "fst (split_memory y r) = getter y r" for r
    by simp

  have [simp]: "fst (split_memory xy r) = (getter x r, getter y r)" for r
    apply (subst fst_split_memory)
    unfolding xy_def by simp_all

  have [simp]: "xrest a = xrest b \<longleftrightarrow> xyrest a = xyrest b \<and> getter y a = getter y b" for a b
    unfolding xrest_def xyrest_def xy_def
    apply (rule split_pair_eq_typed)
    by (rule compat)

  show "A (fst (split_memory x r)) (fst (split_memory x c)) *
           delta (xrest r) (xrest c)
        =
          (\<lambda>(r1, r2) (c1, c2). A r1 c1 * delta r2 c2)
              (fst (split_memory xy r))
              (fst (split_memory xy c))
           *
           delta (xyrest r) (xyrest c)"
    by simp
qed

lemma matrix_on_lift_right:
  assumes compat[simp]: "compatible_lvalues x y"
  defines "xy == lvalue_pair x y"
  shows "matrix_on A y = matrix_on (tensor 1 A) xy"
  sorry

lift_definition map_matrix :: "('b \<Rightarrow> 'a) \<Rightarrow> 'a matrix \<Rightarrow> 'b matrix" is
  "\<lambda>f A r c. A (f r) (f c)".

lift_definition matrix_in :: "'a set \<Rightarrow> 'a matrix \<Rightarrow> bool" is
  "\<lambda>S A. \<forall>r c. A r c \<noteq> 0 \<longrightarrow> r \<in> S \<and> c \<in> S".

lemma matrix_in_UNIV[simp]: "matrix_in UNIV A"
  apply transfer by simp

lift_definition split_matrix :: "('a,'b) lvalue \<Rightarrow> 'a matrix \<Rightarrow> ('b*'a memory_rest) matrix" is
  "\<lambda>x A (r,r') (c,c'). if r' \<in> memory_except x \<and> c' \<in> memory_except x
    then A (join_memory x (r,r')) (join_memory x (c,c')) else 0".

definition "join_matrix x A = map_matrix (split_memory x) A"

lemma map_mult: 
  assumes inj: "inj f"
  assumes "matrix_in (range f) A"
  shows "map_matrix f A * map_matrix f B = map_matrix f (A*B)"
proof (insert assms(2), transfer fixing: f, rule ext, rule ext, rename_tac r c)
  fix A :: "'b \<Rightarrow> 'b \<Rightarrow> complex"
    and B :: "'b \<Rightarrow> 'b \<Rightarrow> complex"
    and r :: 'a
    and c :: 'a
  assume in_range: "\<forall>r c. A r c \<noteq> 0 \<longrightarrow> r \<in> range f \<and> c \<in> range f"
  show "(\<Sum>j\<in>UNIV. A (f r) (f j) * B (f j) (f c)) 
      = (\<Sum>j\<in>UNIV. (A (f r) j) * B j (f c))"
    apply (subst sum.reindex[OF inj, symmetric, unfolded o_def])
    apply (rule sum.mono_neutral_cong_left, auto)
    using in_range by auto
qed
  

(* lift_definition join_matrix :: "('a,'b) lvalue \<Rightarrow> ('b*'a memory_rest) matrix \<Rightarrow> 'a matrix" is
  "\<lambda>x A r c. A (split_memory x r) (split_memory x c)". *)

lift_definition binary_diagonal :: "'a set \<Rightarrow> 'a matrix" is
  "\<lambda>S r c. if r = c \<and> r \<in> S then 1 else 0".

lemma binary_diagonal_square[simp]:
  "binary_diagonal S * binary_diagonal T = binary_diagonal (S \<inter> T)"
proof (transfer fixing: S T , rule ext , rule ext , rename_tac r c)
  fix     r c :: 'a
  have "(\<Sum>j\<in>UNIV. (if r = j \<and> r \<in> S then 1 else (0::complex)) 
                * (if j = c \<and> j \<in> T then 1 else 0))
      = (\<Sum>j\<in>{r}. (if r = j \<and> r \<in> S then 1 else 0) 
                * (if j = c \<and> j \<in> T then 1 else 0))"
    by (rule sum.mono_neutral_cong_right, auto)
  also have "\<dots> = (if r = c \<and> r \<in> S \<inter> T then 1 else 0)"
    apply simp by blast
  finally show "(\<Sum>j\<in>UNIV. (if r = j \<and> r \<in> S then 1::complex else 0) 
                * (if j = c \<and> j \<in> T then 1 else 0)) 
          = (if r = c \<and> r \<in> S \<inter> T then 1 else 0)"
    by -
qed

lemma matrix_in_binary_diagonal[simp]: "matrix_in S (binary_diagonal S)"
  apply transfer by simp

definition matrix_on2 :: "'b matrix \<Rightarrow> ('a,'b) lvalue \<Rightarrow> 'a matrix" where
  "matrix_on2 A x = join_matrix x (tensor A (binary_diagonal (memory_except x)))"

lemma matrix_on2_same:
  assumes "valid_lvalue x"
  shows "matrix_on2 A x = matrix_on A x"
  unfolding matrix_on2_def join_matrix_def
  apply (transfer fixing: x, rule ext, rule ext, rename_tac r c)
  apply (auto simp: case_prod_beta)
  using assms
  by (meson LValues_Typed.split_memory_range mem_Times_iff)


lemma tensor_distrib: "(tensor A B) * (tensor C D) = tensor (A * C) (B * D)"
proof (transfer, rule ext, rule ext)
  fix A C :: "'a\<Rightarrow>'a\<Rightarrow>complex" and B D :: "'b\<Rightarrow>'b\<Rightarrow>complex" and i k :: "'a*'b"
  obtain i1 i2 k1 k2 where i: "i=(i1,i2)" and k: "k=(k1,k2)" by force
  have "(\<Sum>j\<in>UNIV.
          (case i of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). A r1 c1 * B r2 c2) j *
          (case j of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). C r1 c1 * D r2 c2) k)
        =
          (\<Sum>(j1,j2)\<in>UNIV. (A i1 j1 * B i2 j2) * (C j1 k1 * D j2 k2))" (is "?lhs = _")
    unfolding i k by (auto simp: case_prod_beta)
  also have "\<dots> = (\<Sum>j1\<in>UNIV. \<Sum>j2\<in>UNIV. (A i1 j1 * C j1 k1) * (B i2 j2 * D j2 k2))"
    unfolding UNIV_Times_UNIV[symmetric] sum.cartesian_product[symmetric]
    by (meson semiring_normalization_rules(13) sum.cong)
  also have "\<dots> = (\<Sum>j1\<in>UNIV. A i1 j1 * C j1 k1) * (\<Sum>j2\<in>UNIV. B i2 j2 * D j2 k2)"
    by (simp add: sum_product)
  also have "... = (case i of (r1, r2) \<Rightarrow> \<lambda>(c1, c2). (\<Sum>j\<in>UNIV. A r1 j * C j c1) * (\<Sum>j\<in>UNIV. B r2 j * D j c2)) k"  (is "_ = ?rhs")
    unfolding i k by simp
  finally
  show "?lhs = ?rhs" by assumption
qed

lemma matrix_in_tensor: "matrix_in S A \<Longrightarrow> matrix_in T B \<Longrightarrow> matrix_in (S \<times> T) (tensor A B)"
  apply (transfer fixing: S T) by auto

lemma matrix_on_times: 
  fixes x :: "('a::finite,'b::finite) lvalue"
  assumes [simp]: "valid_lvalue x"
  shows "matrix_on A x * matrix_on B x = matrix_on (A*B) x"
proof -
  define spl dia where "spl = split_memory x"
    and "dia = binary_diagonal (LValues_Typed.memory_except x)"

  have inj_spl: "inj spl"
    using assms unfolding spl_def apply transfer 
    apply auto
    using bij_betw_imp_inj_on bij_split_memory by fastforce

  have in_range: "matrix_in (range spl) (tensor A dia)"
    apply (simp add: split_memory_range' spl_def dia_def)
    apply (rule matrix_in_tensor)
    by auto

  have "matrix_on A x * matrix_on B x = matrix_on2 A x * matrix_on2 B x"
    apply (subst matrix_on2_same[symmetric], simp)+ by simp
  also have "\<dots> = map_matrix spl (tensor A dia) * map_matrix spl (tensor B dia)"
    unfolding matrix_on2_def join_matrix_def spl_def[symmetric] dia_def[symmetric] by rule
  also have "\<dots> = map_matrix spl (tensor A dia * tensor B dia)"
    using inj_spl in_range by (rule map_mult)
  also have "\<dots> = map_matrix spl (tensor (A * B) (dia * dia))"
    apply (subst tensor_distrib) by simp
  also have "\<dots> = map_matrix spl (tensor (A * B) dia)"
    unfolding dia_def by simp
  also have "\<dots> = matrix_on2 (A * B) x"
    unfolding matrix_on2_def join_matrix_def spl_def[symmetric] dia_def[symmetric] by rule
  also have "\<dots> = matrix_on (A * B) x"
    by (subst matrix_on2_same[symmetric], auto)
  finally show ?thesis
    by -
qed


lemma
  assumes "compatible_lvalues x y"
  defines "xy == lvalue_pair x y"
  shows "matrix_on A x * matrix_on B y = matrix_on (tensor A B) xy"
proof -
  define splx sply diax diay where "splx = split_memory x"
    and "sply = split_memory y"
    and "diax = binary_diagonal (LValues_Typed.memory_except x)"
    and "diay = binary_diagonal (LValues_Typed.memory_except y)"

  have [simp]: "valid_lvalue x" "valid_lvalue y"
    using compatible_valid1 compatible_valid2 assms(1) by blast+
  have "matrix_on A x * matrix_on B y = matrix_on2 A x * matrix_on2 B y"
    apply (subst matrix_on2_same[symmetric], simp)+ by simp
  also have "\<dots> = map_matrix splx (tensor A diax) * map_matrix sply (tensor B diay)"
    unfolding matrix_on2_def join_matrix_def splx_def[symmetric] sply_def[symmetric]
        diax_def[symmetric] diay_def[symmetric] by rule
  

  show ?thesis
    by -
qed

end
