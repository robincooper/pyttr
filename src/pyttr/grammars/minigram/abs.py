"""Abstract mini grammar from ``~/oz/ttr-tool/python/src/ttrtool/grammars/``."""

"""Abstract mini grammar from ``ttr01/grammars/mini/minigram-abs.oz``."""

from ttrtool.grammars.ures_abs import lex, rule_binary, rule_unary

kim = lex("Kim", "np")
sandy = lex("Sandy", "np")
pron = lex("Pron", "np")
indef_art = lex("IndefArt", "det")
man = lex("Man", "n")
donkey = lex("Donkey", "n")
run = lex("Run", "vp")
like = lex("Like", "v")
own = lex("Own", "v")

s_np_vp = rule_binary("s_np_vp", "s", "np", "vp")
np_det_n = rule_binary("np_det_n", "np", "det", "n")
vp_v_np = rule_binary("vp_v_np", "vp", "v", "np")
d_d_s = rule_binary("d_d_s", "d", "d", "s")
d_s = rule_unary("d_s", "d", "s")

lexicon = (kim, sandy, pron, indef_art, man, donkey, run, like, own)
rules = (s_np_vp, np_det_n, vp_v_np, d_d_s, d_s)

