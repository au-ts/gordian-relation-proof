import sys

STANDALONE = len(sys.argv) >= 2 and sys.argv[1] == '--standalone'

if STANDALONE:
    print("""
    (set-logic ALL)
(declare-datatype Ch (
    (Ch00) (Ch01) (Ch02) (Ch03) (Ch04) (Ch05) (Ch06) (Ch07) (Ch08) (Ch09)
    (Ch10) (Ch11) (Ch12) (Ch13) (Ch14) (Ch15) (Ch16) (Ch17) (Ch18) (Ch19)
    (Ch20) (Ch21) (Ch22) (Ch23) (Ch24) (Ch25) (Ch26) (Ch27) (Ch28) (Ch29)
    (Ch30) (Ch31) (Ch32) (Ch33) (Ch34) (Ch35) (Ch36) (Ch37) (Ch38) (Ch39)
    (Ch40) (Ch41) (Ch42) (Ch43) (Ch44) (Ch45) (Ch46) (Ch47) (Ch48) (Ch49)
    (Ch50) (Ch51) (Ch52) (Ch53) (Ch54) (Ch55) (Ch56) (Ch57) (Ch58) (Ch59)
    (Ch60) (Ch61) (Ch62)
))

(define-sort Word64 () (_ BitVec 64))
(declare-datatype Maybe (par (X) ((Nothing) (Just (just X)))))
(declare-datatype Prod (par (X Y) ((Prod (fst X) (snd Y)))))
"""
    )

NUM_CH = 63

def put(*args, **kwargs):
    print('   ', *args, **kwargs)

print(f"; AUTO GENERATED from {__file__}")


put("(define-fun ch2word ((ch Ch)) Word64 (match ch (")
for i in range(0, NUM_CH):
    put(f"    (Ch{i:02} (_ bv{i} 64))")

put(")))")

put("(define-fun word2ch ((wch Word64)) (Maybe Ch) ")
for i in range(0, NUM_CH):
    put(f"  (ite (= wch (_ bv{i} 64)) (Just Ch{i:02})")

put(f"  (as Nothing (Maybe Ch))")
put(")" * (NUM_CH + 1))

put(f"(define-fun word_is_valid_ch ((wch Word64)) Bool ((_ is Just) (word2ch wch)))")

if STANDALONE:
    put("; TODO: test they are indeed inverse of each other")
    # put("(push)")
    # put("""
    # (declare-const ch Ch)
    # (declare-const wch Word64)
    # (assert (not (and (ch2word ch))))
    # (check-sat)
    # """)
    # put("    (declare-const ch Ch)")
    # put("    (declare-const wch Word64)")
    # put("    (assert (not (and)))")
    # put("    (check-sat)")
    # put("(pop)")

print("; END OF AUTO GENERATED")
