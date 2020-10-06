theory Necessary
  imports Computation
begin

locale necessary' = fnft: fNFT ninit n\<delta> naccept nQ + koTDFA init \<delta> accept Q
  for ninit :: "'s"
  and n\<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and naccept :: "'s \<Rightarrow> bool"
  and nQ :: "'s set"
  and init :: "'t"
  and \<delta> :: "'t \<Rightarrow> ('a :: finite) Al \<times> 'b Al \<Rightarrow> ('t \<times> bool \<times> bool) option"
  and accept :: "'t \<Rightarrow> bool"
  and Q :: "'t set" +
assumes equiv: "fnft.\<tau> = \<tau>"
begin

abbreviation f\<delta> :: "'t \<Rightarrow> 'b Al \<times> 'a Al \<Rightarrow> ('t \<times> bool \<times> bool) option" where
  "f\<delta> \<equiv> (\<lambda>q (b, a). case \<delta> q (a, b) of None \<Rightarrow> None | Some (q', b1, b2) \<Rightarrow> Some (q', b2, b1))"

interpretation flip: oTDFA init f\<delta> accept Q
  using finite_Q init_in_Q closed move_left move_right no_step move_one
  apply unfold_locales
        apply (auto split: option.splits)
     apply fastforce+
  done

lemma flip_comp_intro: "q \<leadsto>(as, bs) q' \<Longrightarrow> flip.computation q (bs, as) q'"
  by (induction q "(as, bs)" q' arbitrary: as bs rule: computation.induct) auto

lemma flip_comp_dest: "flip.computation q (bs, as) q' \<Longrightarrow> q \<leadsto>(as, bs) q'"
  by (induction q "(bs, as)" q' arbitrary: as bs rule: flip.computation.induct)
     (auto split: option.splits)

lemma flip_comp_eq: "flip.computation q (bs, as) q' \<longleftrightarrow> q \<leadsto>(as, bs) q'"
  using flip_comp_intro flip_comp_dest
  by blast

lemmas flip_comp_to_states = flip.comp_to_states[unfolded flip_comp_eq]
lemmas flip_states_to_comp = flip.states_to_comp[unfolded flip_comp_eq]
lemmas flip_split_outs = flip.split_outs[unfolded flip_comp_eq]

lemma split_long:
  assumes "length w \<ge> n"
  shows "\<exists>v' v''. w = v' @ v'' \<and> length v'' = n"
  using assms
  by (metis append_take_drop_id diff_diff_cancel length_drop)

lemma concat_filter: "length qbs = length xs \<Longrightarrow> length ns = length xs \<Longrightarrow>
  concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) (filter (\<lambda>(n, (q, bs), (bs', q')). bs \<noteq> [])
  (zip ns (zip qbs xs)))) = concat (map snd qbs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma concat_length: "(\<And>n q bs bs' q'. (n, (q, bs), (bs', q')) \<in> set qss' \<Longrightarrow> length bs \<le> d) \<Longrightarrow>
  length (concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss')) \<le> length qss' * d"
  by (induction qss') fastforce+

lemma sorted_dest: "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow> i < j \<Longrightarrow> j < length xs \<Longrightarrow> xs ! i < xs ! j"
  by (simp add: less_le nth_eq_iff_index_eq sorted_iff_nth_mono_less)

lemma map2_zip: "length qbs = length xs \<Longrightarrow> length qbs = length ns \<Longrightarrow>
  qbs = map2 (\<lambda>n ((q, bs), (bs', q')). (q, bs)) ns (zip qbs xs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma map2_zip': "length qbs = length xs \<Longrightarrow> length qbs = length ns \<Longrightarrow>
  xs = map2 (\<lambda>n ((q, bs), (bs', q')). (bs', q')) ns (zip qbs xs)"
  apply (induction qbs xs arbitrary: ns rule: list_induct2)
   apply auto[1]
  subgoal for x xs y ys ns
    by (cases ns) auto
  done

lemma split_one: "n < length xs \<Longrightarrow> \<exists>ys ys'. xs = ys @ (xs ! n) # ys' \<and>
  length ys = n \<and> length ys' = length xs - (n + 1)"
  apply (induction n arbitrary: xs)
  subgoal for xs
    by (cases xs) auto
  subgoal for n xs
    apply (cases xs)
     apply auto
    apply (metis append_Cons length_Cons)
    done
  done

lemma split_two: "n < n' \<Longrightarrow> n' < length xs \<Longrightarrow>
  \<exists>ys ys' ys''. xs = ys @ (xs ! n) # ys' @ (xs ! n') # ys'' \<and> length ys = n \<and>
  length ys' = n' - (n + 1) \<and> length ys'' = length xs - (n' + 1)"
proof (induction n arbitrary: n' xs)
  case 0
  then show ?case
  proof (cases xs)
    case (Cons x xs')
    then show ?thesis
      using 0 split_one[of "n' - 1" xs']
      by auto
  qed auto
next
  case (Suc n)
  then show ?case
  proof (cases xs)
    case (Cons x xs')
    have n'_shift: "n < n' - 1" "n' - 1 < length xs'"
      using Suc(2,3)
      by (auto simp add: Cons)
    then obtain ys ys' ys'' where split: "xs' = ys @ xs' ! n # ys' @ xs' ! (n' - 1) # ys''"
      "length ys = n" "length ys' = n' - (Suc n + 1)" "length ys'' = length xs - (n' + 1)"
      using Suc(1)[OF n'_shift]
      by (auto simp add: Cons)
    show ?thesis
      apply (rule exI[of _ "x # ys"])
      using split Suc(2)
      by (auto simp add: Cons)
  qed auto
qed  

lemma joint_rem:
  assumes "fnft.computation s (as, bs) s'" "s \<in> nQ"
    "length bs > card nQ * card Q * fnft.output_speed"
    "flip.computation q (([], bss''), (as, as'')) q''" "q \<in> Q"
    "length as > card nQ * card Q"
  shows "\<exists>as' bs'. fnft.computation s (as', bs') s' \<and>
    flip.computation q (([], bss''), (as', as'')) q'' \<and>
    safe_hd as' = safe_hd as \<and> length bs' < length bs"
proof -
  obtain qbs where qbs_def: "fnft.computation_ext s (as, qbs) s'" "bs = concat (map snd qbs)"
    using fnft.computation_ext_complete[OF assms(1)]
    by auto
  note qbs_output_speed = fnft.output_speed_ext_computation[OF qbs_def(1) assms(2)]
  have len_qbs: "length qbs = length as"
    using fnft.computation_ext_length[OF qbs_def(1)]
    by auto
  obtain tqs where tqs_def: "flip.computation_ext q (tqs, ([], bss''), (as, as'')) q''"
    using flip.comp_to_ext[OF assms(4)]
    by auto
  have len_tqs: "length tqs = length as"
    using flip.comp_ext_length[OF tqs_def]
    by auto
  define xs where "xs = zip tqs as"
  have len_xs: "length xs = length as"
    by (auto simp: xs_def len_tqs)
  define qss where "qss = zip [0..<length qbs] (zip qbs xs)"
  have len_qbs_xs: "length qbs = length xs"
    using len_qbs len_xs
    by auto
  have len_qss: "length qss = length qbs"
    using len_qbs
    by (auto simp: qss_def len_xs)
  have fst_qss_at: "\<And>i. i < length qss \<Longrightarrow> fst (qss ! i) = i"
    using len_qbs
    by (auto simp add: qss_def)
  have fst_set_qss: "\<And>x. x \<in> set qss \<Longrightarrow> fst x < length qss"
    using len_qbs_xs
    by (auto simp add: qss_def dest: set_zip_leftD set_zip_rightD)
  define qss' where "qss' = filter (\<lambda>(n, (q, bs), (q', b)). bs \<noteq> []) qss"
  have fst_set_qss': "\<And>x. x \<in> set qss' \<Longrightarrow> x \<in> set qss"
    by (auto simp add: qss'_def)
  define qs where "qs = map (\<lambda>(n, (q, bs), (q', b)). (q, q')) qss'"
  have qss'_at: "\<And>i. i < length qss' \<Longrightarrow>
    fst (qss' ! i) < length qss \<and> qss' ! i = qss ! (fst (qss' ! i))"
    using fst_qss_at fst_set_qss' fst_set_qss
    by auto (metis fst_set_qss' in_set_conv_nth)
  have qss'_nonempty: "\<And>n q bs bs' q'. (n, (q, bs), (bs', q')) \<in> set qss' \<Longrightarrow> bs \<noteq> []"
    by (auto simp add: qss'_def)
  have sorted_fst_qss: "sorted (map fst qss)" "distinct (map fst qss)"
    using len_qbs_xs
    by (auto simp add: qss_def)
  have sorted_fst_qss': "sorted (map fst qss')" "distinct (map fst qss')"
    unfolding qss'_def
    by (rule sorted_filter[OF sorted_fst_qss(1)])
       (rule distinct_map_filter[OF sorted_fst_qss(2)])
  have len_qs: "length qs = length qss'"
    by (auto simp add: qs_def)
  have qs_sub: "set qs \<subseteq> nQ \<times> Q"
    using fnft.computation_ext_closed[OF qbs_def(1) assms(2)] flip.ext_closed[OF tqs_def assms(5)]
      len_qbs_xs
    by (fastforce simp: qs_def qss'_def qss_def xs_def dest: set_zip_leftD set_zip_rightD)
  have concat_qss': "concat (map (\<lambda>(n, (q, bs), (q', b)). bs) qss') = concat (map snd qbs)"
    using concat_filter[of _ _ "[0..<length qbs]"] len_qbs_xs
    by (auto simp add: qss'_def qss_def)
  have len_qs_ge: "length qs \<ge> 1 + card nQ * card Q"
  proof (rule ccontr)
    assume lassm: "\<not> length qs \<ge> 1 + card nQ * card Q"
    have "length (concat (map (\<lambda>(n, (q, bs), (bs', q')). bs) qss')) \<le>
      length qss' * fnft.output_speed"
      apply (rule concat_length[of qss' fnft.output_speed])
      using qbs_output_speed
      by (auto simp add: qss'_def qss_def dest: set_zip_leftD set_zip_rightD)
    then show "False"
      using fnft.output_speed_pos assms(3) lassm less_le_trans
      by (fastforce simp add: arg_cong[OF concat_qss', of length] qbs_def(2)[symmetric]
          len_qs[symmetric])
  qed
  have not_distinct: "\<not> distinct qs"
  proof (rule ccontr)
    assume "\<not>\<not> distinct qs"
    then have contr: "distinct qs"
      by auto
    have card_qs: "card (set qs) \<ge> 1 + card nQ * card Q"
      using distinct_card[OF contr] len_qs_ge
      by (auto simp add: qs_def)
    have finite_prod: "finite (nQ \<times> Q)"
      using fnft.finite_Q finite_Q
      by blast
    have card_prod: "card (nQ \<times> Q) = card nQ * card Q"
      using card_cartesian_product
      by blast
    show "False"
      using card_qs card_mono[OF finite_prod qs_sub]
      by (auto simp add: card_prod)
  qed
  obtain qc qs' qs'' qs''' where qs_split: "qs = qs' @ [qc] @ qs'' @ [qc] @ qs'''"
    using not_distinct_decomp[OF not_distinct]
    by auto
  define n where "n = fst (qss' ! length qs')"
  define n' where "n' = fst (qss' ! (length qs' + 1 + length qs''))"
  have valid_idx: "length qs' < length qss'" "length qs' + 1 + length qs'' < length qss'"
    using qs_split len_qs len_qss
    by auto
  have qs_split_at: "qs ! (length qs') = qc" "qs ! (length qs' + 1 + length qs'') = qc"
    using qs_split
     apply auto
    by (metis add_Suc_right nth_Cons_Suc nth_append_length nth_append_length_plus)
  have n_n': "n < n'" "n' < length qbs" "qss ! n = qss' ! length qs'"
    "qss ! n' = qss' ! (length qs' + 1 + length qs'')"
    using qss'_at[OF valid_idx(1), folded n_def] qss'_at[OF valid_idx(2), folded n'_def]
          len_qss valid_idx sorted_dest[OF sorted_fst_qss']
    by (auto simp add: n_def n'_def)
  have qbs_map: "qbs = map (\<lambda>(n, (q, bs), (q', b)). (q, bs)) qss"
    using map2_zip[OF len_qbs_xs, of "[0..<length qbs]"]
    by (auto simp add: qss_def)
  obtain qbs' qbs'' qbs''' where decomp: "qbs = qbs' @ qbs ! n # qbs'' @ qbs ! n' # qbs'''"
    "length qbs' = n" "length qbs'' = n' - (n + 1)" "length qbs''' = length qbs - (n' + 1)"
    using split_two[OF n_n'(1,2)]
    by auto
  obtain bs' where bs'_def: "qbs ! n = (fst qc, bs')"
    using qbs_map n_n' qs_def len_qs qs_split_at(1) valid_idx(1)
    by (auto split: prod.splits)
  obtain bs'' where bs''_def: "qbs ! n' = (fst qc, bs'')" "bs'' \<noteq> []"
    using qbs_map n_n' qs_def len_qs qs_split_at(2) valid_idx(2) qss'_nonempty
    by (auto split: prod.splits) (metis in_set_conv_nth)
  obtain cs' cs'' cs''' c' c'' bs'a bs''' where new_comp:
    "fnft.computation s (cs' @ c' # cs''', bs'a @ bs' @ bs''') s'"
    "bs'a = concat (map snd qbs')" "bs''' = concat (map snd qbs''')"
    "as = cs' @ c' # cs'' @ c'' # cs'''" "length cs' = length qbs'" "length cs'' = length qbs''"
    "length cs''' = length qbs'''"
    using fnft.computation_ext_rem[OF qbs_def(1)[unfolded decomp(1)[unfolded bs'_def bs''_def]]]
    by auto
  have new_length: "length (bs'a @ bs' @ bs''') < length bs"
    apply (auto simp add: new_comp(2,3) qbs_def(2))
    apply (subst decomp(1))
    apply (auto simp add: bs'_def bs''_def)
    done
  have xs_map: "xs = map (\<lambda>(n, (q, bs), (q', b)). (q', b)) qss"
    using map2_zip'[OF len_qbs_xs, of "[0..<length qbs]"]
    by (auto simp add: qss_def)
  obtain xs' xs'' xs''' where decomp': "xs = xs' @ xs ! n # xs'' @ xs ! n' # xs'''"
    "length xs' = n" "length xs'' = n' - (n + 1)" "length xs''' = length xs - (n' + 1)"
    using split_two[OF n_n'(1) n_n'(2)[unfolded len_qbs_xs]]
    by auto
  obtain b where b_def: "xs ! n = (snd qc, b)"
    using xs_map n_n'[unfolded len_qbs_xs] qs_def len_qs qs_split_at(1) valid_idx(1)
    by (auto split: prod.splits)
  obtain b' where b'_def: "xs ! n' = (snd qc, b')"
    using xs_map n_n'[unfolded len_qbs_xs] qs_def len_qs qs_split_at(2) valid_idx(2)
    by (auto split: prod.splits)
  have tqs_xs: "tqs = map fst xs"
    using len_tqs
    by (auto simp: xs_def)
  have assoc: "flip.computation_ext q
    (map fst xs' @ snd qc # map fst xs'' @ snd qc # map fst xs''', ([], bss''), as, as'') q''"
    using tqs_def[unfolded tqs_xs decomp'(1)[unfolded b_def b'_def]]
    by simp
  have as_xs: "as = map snd xs"
    using len_tqs
    by (auto simp: xs_def)
  have as_xs': "as = map snd xs' @ b # map snd xs'' @ b' # map snd xs'''"
    using len_tqs arg_cong[OF decomp'(1)[unfolded b_def b'_def], of "map snd"]
    by (auto simp: xs_def)
  note assoc_rem = flip.ext_rem_loop[OF assoc[unfolded as_xs'], simplified]
  have "cs' @ c' # cs''' = map snd xs' @ b # map snd xs'''"
    using new_comp(4)[symmetric] new_comp(5,6) decomp'(2,3)
    by (auto simp: decomp(2,3) as_xs')
  moreover have "safe_hd (map snd xs' @ b # map snd xs''') = safe_hd as"
    using safe_hd_eq[OF decomp'(1)[unfolded b_def]]
    by (auto simp: as_xs)
  ultimately show ?thesis
    using new_comp(1) new_length flip.ext_to_comp[OF assoc_rem]
    unfolding as_xs
    by (fastforce simp: as_xs)
qed

lemma card_nQ_pos: "card nQ \<ge> 1"
  using fnft.finite_Q fnft.init_in_Q
  by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)

lemma card_Q_pos: "card Q \<ge> 1"
  using finite_Q init_in_Q
  by (metis One_nat_def Suc_leI card_gt_0_iff empty_iff)

lemma card_nQ_Q_pos: "card nQ * card Q \<ge> 1"
  using card_nQ_pos card_Q_pos
  by auto

lemma mult_all: "x \<le> card nQ * card Q * fnft.output_speed * x"
  using card_nQ_Q_pos fnft.output_speed_pos
  by auto

lemma conflict:
  assumes "fnft.computation s (as, bs @ bs') s'" "r \<leadsto>((as, us), (bs', vs)) r'" "s \<in> nQ" "r \<in> Q"
    "length bs + length bs' > card nQ * card Q * fnft.output_speed * (1 + length bs')"
  shows "\<exists>as' bs''. fnft.computation s (as', bs'') s' \<and> r \<leadsto>((as', us), (bs', vs)) r' \<and>
    safe_hd as = safe_hd as' \<and> length bs'' < length (bs @ bs')"
  using assms
proof (induction bs' arbitrary: s as bs r)
  case Nil
  have len_as: "card nQ * card Q < length as"
    using less_le_trans[OF Nil(5)[simplified]
          fnft.output_speed_computation[OF Nil(1,3), simplified]]
          fnft.output_speed_pos
    by auto
  obtain as' bs' where rem: "fnft.computation s (as', bs') s'"
    "flip.computation r (([], vs), as', us) r'"
    "safe_hd as' = safe_hd as" "length bs' < length (bs @ [])"
    using joint_rem[OF Nil(1,3) _ iffD2[OF flip_comp_eq, OF Nil(2)] Nil(4) len_as] Nil(5)
    by auto
  note rem' = iffD1[OF flip_comp_eq, OF rem(2)]
  show ?case
    using rem(1) rem' rem(3,4)
    by fastforce
next
  case (Cons b bs')
  obtain r'a r'b cs cs' where outs: "as = cs @ cs'"
    "case cs of [] \<Rightarrow> r = r'a | _ \<Rightarrow> r \<leadsto>((cs, cs' @ us), ([], b # bs' @ vs)) r'a"
    "f\<delta> r'a (Symb b, safe_hd (cs' @ us)) = Some (r'b, True, False)"
    "r'b \<leadsto>((cs', us), bs', vs) r'"
    using flip_split_outs[OF Cons(3)]
    by auto
  have r'b_Q: "r'b \<in> Q"
    using Cons(5) outs(2,3,4) closed comp_closed[OF _ Cons(5)]
    by (auto split: list.splits option.splits) blast
  have len_as: "length as \<ge> card nQ * card Q * (2 + length bs')"
  proof -
    have "card nQ * card Q * (2 + length bs') * fnft.output_speed \<le> length (bs @ b # bs')"
      using Cons(6)
      by (subst semiring_normalization_rules(16)) auto
    then show ?thesis
      using fnft.output_speed_computation[OF Cons(2,4)] fnft.output_speed_pos
      by (metis (no_types, lifting) One_nat_def Suc_le_eq le_trans mult_le_cancel2)
  qed
  obtain q' ds ds' where split:
    "fnft.computation s (cs, ds) q'"
    "fnft.computation q' (cs', ds') s'"
    "bs @ b # bs' = ds @ ds'"
    using fnft.computation_split[OF Cons(2)[unfolded outs(1)]]
    by auto
  note q'_nQ = fnft.comp_closed[OF split(1) Cons(4)]
  show ?case
  proof (cases "card nQ * card Q * fnft.output_speed < length ds")
    case True
    have len_as: "card nQ * card Q < length cs"
    proof -
      have "card nQ * card Q * fnft.output_speed < length cs * fnft.output_speed"
        using Cons(6) less_le_trans[OF True fnft.output_speed_computation[OF split(1) Cons(4)]]
        by auto
      then show ?thesis
        using fnft.output_speed_pos
        by auto
    qed
    then have comp_r_r'a: "r \<leadsto>((cs, cs' @ us), ([], b # bs' @ vs)) r'a"
      using outs(2)
      by (auto split: list.splits)
    obtain as'' bs'' where rem: "fnft.computation s (as'', bs'') q'"
      "flip.computation r (([], b # bs' @ vs), as'', cs' @ us) r'a"
      "safe_hd as'' = safe_hd cs" "length bs'' < length ds"
      using joint_rem[OF split(1) Cons(4) True iffD2[OF flip_comp_eq, OF comp_r_r'a] Cons(5) len_as]
      by auto
    have "r\<leadsto>((as'' @ cs', us), b # bs', vs)r'"
      using flip.comp_trans[OF rem(2) flip.step_TF[OF outs(3) iffD2[OF flip_comp_eq, OF outs(4)]]]
      by (auto simp: flip_comp_eq)
    then show ?thesis
      using fnft.comp_trans[OF rem(1) split(2)] safe_hd_app[OF rem(3), of cs'] split(3) rem(4)
      by (auto simp: outs(1) intro!: exI[of _ "as'' @ cs'"] exI[of _ "bs'' @ ds'"])
  next
    case False
    have len_bs_ds: "length ds \<le> length (bs @ [b])"
      using False mult_all[of "length (b # bs')"] Cons(6)
      by auto
    obtain es where es_def: "ds' = es @ bs'"
      using split(3) split_app'[OF _ len_bs_ds]
      by fastforce
    have bs_ds_es: "bs @ [b] = ds @ es"
      using split(3)[unfolded es_def]
      by auto
    have len_es: "card nQ * card Q * fnft.output_speed * (1 + length bs') < length es + length bs'"
    proof -
      have "card nQ * card Q * fnft.output_speed * (1 + length bs') + length ds \<le>
        card nQ * card Q * fnft.output_speed * (1 + length bs') +
        card nQ * card Q * fnft.output_speed"
        using False
        by auto
      also have "\<dots> < length ds + length es + length bs'"
        using arg_cong[OF bs_ds_es, of length] Cons(6)
        by auto
      finally show ?thesis
        by auto
    qed
    obtain as'' bs'' where rest: "fnft.computation q' (as'', bs'') s'"
      "r'b\<leadsto>((as'', us), bs', vs)r'" "safe_hd cs' = safe_hd as''" "length bs'' < length (es @ bs')"
      using Cons(1)[OF split(2)[unfolded es_def] outs(4) q'_nQ r'b_Q len_es]
      by auto
    have new_length: "length (ds @ bs'') < length (bs @ b # bs')"
      using rest(4)
      by (auto simp add: split(3) es_def)
    note safe_hd_cs' = safe_hd_app[OF rest(3)]
    have comp_r_r': "r \<leadsto>((cs @ as'', us), b # bs', vs) r'"
      using outs(2) flip.step_TF[OF outs(3)[unfolded safe_hd_cs']] rest(2)
        comp_trans[OF _ _ safe_hd_cs' refl, of r _ us "[]" "b # bs'" vs r'a r']
      by (fastforce simp: flip_comp_eq split: list.splits)
    have "safe_hd as = safe_hd (cs @ as'')"
      using safe_hd_app'[OF rest(3)[unfolded outs(4)]]
      by (auto simp add: outs(1))
    then show ?thesis
      using fnft.comp_trans[OF split(1) rest(1)] new_length comp_r_r'
      by fastforce
  qed
qed

lemma bounded: "\<exists>K. fnft.bounded K"
proof (rule ccontr)
  (* home stretch *)
  define h where "h = (fnft.sg + 1) * (card Q + 1)"
  (* trail length *)
  define t where "t = card nQ * card Q * fnft.output_speed *
    (h + (fnft.sg + 1) * fnft.output_speed + 1)"
  assume "\<not>(\<exists>K. fnft.bounded K)"
  then obtain q q' u v w where unbounded: "fnft.computation ninit (u, v @ w) q"
    "fnft.active q []" "fnft.computation ninit (u, v) q'" "fnft.active q' w"
    "length w > t"
    by (auto simp add: fnft.bounded_def) (metis less_or_eq_imp_le neqE)
  note q_nQ = fnft.comp_closed[OF unbounded(1) fnft.init_in_Q]
  note q'_nQ = fnft.comp_closed[OF unbounded(3) fnft.init_in_Q]
  obtain u1 v1 nqf where ext: "fnft.computation q (u1, v1) nqf" "naccept nqf"
    "length u1 \<le> fnft.sg" "length v1 \<le> fnft.sg * fnft.output_speed"
    using fnft.active_Nil_dest_sg[OF unbounded(2) q_nQ]
    by auto
  obtain u2 v2 nqf' where ext': "fnft.computation q' (u2, w @ v2) nqf'" "naccept nqf'"
    "length v2 \<le> (1 + fnft.sg) * fnft.output_speed"
    using fnft.active_dest[OF unbounded(4) q'_nQ]
    by auto
  note len_w_gt = le_less_trans[OF mult_all[of "h + (fnft.sg + 1) * fnft.output_speed + 1"]
      unbounded(5)[unfolded t_def]]
  have len_w: "length w \<ge> h"
    using len_w_gt
    by auto
  obtain v' v'' where w_def: "w = v' @ v''" "length v'' = h"
    using split_long[OF len_w]
    by auto
  have "fnft.computation ninit (u @ u1, (v @ v') @ v'' @ v1) nqf"
    using fnft.comp_trans[OF unbounded(1) ext(1), unfolded w_def]
    by auto
  then obtain qf where qf_def: "init \<leadsto>((u @ u1, []), ((v @ v') @ v'' @ v1, [])) qf" "accept qf"
    using ext(2) equiv
    by (fastforce simp add: fnft.\<tau>_def \<tau>_def)
  have "fnft.computation ninit (u @ u2, (v @ v') @ v'' @ v2) nqf'"
    using fnft.comp_trans[OF unbounded(3) ext'(1), unfolded w_def]
    by auto
  then obtain qf' where qf'_def: "init \<leadsto>((u @ u2, []), ((v @ v') @ v'' @ v2, [])) qf'"
    "accept qf'"
    using ext'(2) equiv
    by (fastforce simp add: fnft.\<tau>_def \<tau>_def)
  have u_not_Nil: "u \<noteq> []"
    using fnft.output_speed_computation[OF unbounded(1) fnft.init_in_Q]
      unbounded(5)[unfolded t_def]
    by auto
  have v''_not_Nil: "v'' \<noteq> []"
    using w_def(2)[unfolded h_def]
    by auto
  then have safe_hd_v'': "safe_hd (v'' @ v1) = safe_hd (v'' @ v2)"
    using safe_hd_app''[OF v''_not_Nil]
    by auto
  have safe_hd_u1_u2: "safe_hd (u @ u1) = safe_hd (u @ u2)"
    using safe_hd_app''[OF u_not_Nil]
    by auto
  have u_Nil_contr: "u \<noteq> [] \<or> v @ v' \<noteq> []"
    by (auto simp: u_not_Nil)
  show "False"
    using first_reaches[OF qf_def(1), OF u_Nil_contr]
  proof (rule disjE)
    assume "\<exists>ws ws' q''. v @ v' = ws @ ws' \<and> ws' \<noteq> [] \<and>
      init \<leadsto>((u, u1 @ []), ws, ws' @ (v'' @ v1) @ []) q'' \<and>
      q'' \<leadsto>((u1, []), ws' @ v'' @ v1, []) qf"
    then obtain ws ws' q'' where tail: "v @ v' = ws @ ws'"
      "init \<leadsto>((u, u1 @ []), ws, ws' @ (v'' @ v1) @ []) q''"
      "q'' \<leadsto>((u1 @ [], []), ws' @ (v'' @ v1) @ [], []) qf"
      by auto
    have le: "(length (u1 @ []) + 1) * card Q \<le> (fnft.sg + 1) * card Q"
      using ext(3)
      by auto
    show "False"
      using le_trans[OF lin_bounded[OF tail(2,3) qf_def(2)] le] w_def(2)
      unfolding h_def
      by auto
  next
    assume "\<exists>ws ws' q''. u = ws @ ws' \<and> ws' \<noteq> [] \<and>
      init\<leadsto>((ws, ws' @ u1 @ []), v @ v', (v'' @ v1) @ [])q'' \<and>
      q''\<leadsto>((ws' @ u1, []), v'' @ v1, [])qf"
    then obtain ws ws' q'' where tail': "u = ws @ ws'" "ws' \<noteq> []"
      "init \<leadsto>((ws, ws' @ u1 @ []), v @ v', (v'' @ v1) @ []) q''"
      "q'' \<leadsto>((ws' @ u1, []), v'' @ v1, []) qf"
      by auto
    obtain f fs where u2_def: "u2 = f # fs"
      using fnft.output_speed_computation[OF ext'(1) q'_nQ] len_w_gt
      by (cases u2) auto
    have comp_init_q'': "init \<leadsto>((ws, ws' @ u2 @ []), v @ v', (v'' @ v2) @ []) q''"
      by (rule comp_swap_same_hd[OF tail'(3)])
         (simp add: safe_hd_app'' tail'(2) v''_not_Nil)+
    have comp_q''_qf': "q'' \<leadsto>((ws' @ f # fs, []), (v'' @ v2, [])) qf'"
      using comp_pull[OF comp_init_q''] qf'_def(1)
      by (simp add: tail'(1) u2_def)
    obtain r ds ds' where tail: "q'' \<leadsto>((ws', f # fs), (ds, ds')) r"
      "r \<leadsto>((f # fs, []), (ds', [])) qf'" "v'' @ v2 = ds @ ds'"
      using comp_split[OF comp_q''_qf']
      by auto
    note r_Q = comp_closed[OF tail(1) comp_closed[OF tail'(3) init_in_Q]]
    have comp': "fnft.computation q' (f # fs, (v' @ ds) @ ds') nqf'"
      using ext'(1)[unfolded w_def u2_def, simplified] tail(3)
      by auto
    have len_ds': "length ds' \<le> h + (fnft.sg + 1) * fnft.output_speed"
      using arg_cong[OF tail(3), of length] w_def(2) ext'(3)
      by auto
    have len_v': "card nQ * card Q * fnft.output_speed * (1 + length ds') < length (v' @ ds @ ds')"
    proof -
      have "card nQ * card Q * fnft.output_speed * (1 + length ds') \<le> t"
        using len_ds'
        by (auto simp add: t_def)
      also have "\<dots> < length (v' @ v'')"
        using unbounded(5)[unfolded w_def(1)] .
      finally show ?thesis
        by (auto simp add: tail(3)[symmetric])
    qed
    obtain as' bs'' where rem: "fnft.computation q' (as', bs'') nqf'"
      "r \<leadsto>((as', []), (ds', [])) qf'"
      "safe_hd (f # fs) = safe_hd as'" "length bs'' < length ((v' @ ds) @ ds')"
      using conflict[OF comp' tail(2) q'_nQ r_Q] len_v'
      by auto
    have wit1: "(u @ as', v @ bs'') \<in> \<tau>"
      using fnft.comp_trans[OF unbounded(3) rem(1)] ext'(2) fnft.\<tau>_def equiv
      by auto
    have wit2: "(u @ as', v @ v' @ ds @ ds') \<in> \<tau>"
      using comp_trans[OF comp_trans[OF comp_init_q'' tail(1)] rem(2)] qf'_def(2)
      by (auto simp: tail'(1) rem(3) tail(3) u2_def \<tau>_def)
    show "False"
      using fnft.functional[unfolded equiv, OF wit1 wit2] rem(4)
      by auto
  qed
qed

end

locale necessary = fnft: fNFT ninit n\<delta> naccept nQ + koTDFA init \<delta> accept Q
  for ninit :: "'s"
  and n\<delta> :: "'s \<Rightarrow> 'a :: finite \<Rightarrow> 's \<times> 'b list \<Rightarrow> bool"
  and naccept :: "'s \<Rightarrow> bool"
  and nQ :: "'s set"
  and init :: "'t"
  and \<delta> :: "'t \<Rightarrow> ('a :: finite) Al \<times> 'b Al \<Rightarrow> ('t \<times> bool \<times> bool) option"
  and accept :: "'t \<Rightarrow> bool"
  and Q :: "'t set" +
assumes equiv: "fnft.\<tau> = \<tau>"
begin

interpretation otdfa: oTDFA otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using otdfa_finite_Q otdfa_init_in_Q otdfa_closed[rotated]
        otdfa_move_left otdfa_move_right otdfa_no_step otdfa_move_one
  by unfold_locales auto

interpretation nec: necessary' 1 ninit n\<delta> naccept nQ otdfa_init otdfa_delta otdfa_accept otdfa_Q
  using fnft.one_valued
  by unfold_locales (auto simp add: equiv tdfa_equiv_otdfa)

(* Theorem 10 *)

lemma bounded: "\<exists>K. fnft.bounded K"
  using nec.bounded .

end

end
