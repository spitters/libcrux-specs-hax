
-- Experimental lean backend for Hax
-- The Hax prelude library can be found in hax/proof-libs/lean
import Hax
import Std.Tactic.Do
import Std.Do.Triple
import Std.Tactic.Do.Syntax
open Std.Do
open Std.Tactic

set_option mvcgen.warning false
set_option linter.unusedVariables false


namespace Libcrux_specs_hax.Sha256

--  SHA-256 round constants (first 32 bits of the fractional parts of the
--  cube roots of the first 64 primes).
def K_TABLE : (RustArray u32 64) :=
  RustM.of_isOk
    (do
    #v[(1116352408 : u32),
         (1899447441 : u32),
         (3049323471 : u32),
         (3921009573 : u32),
         (961987163 : u32),
         (1508970993 : u32),
         (2453635748 : u32),
         (2870763221 : u32),
         (3624381080 : u32),
         (310598401 : u32),
         (607225278 : u32),
         (1426881987 : u32),
         (1925078388 : u32),
         (2162078206 : u32),
         (2614888103 : u32),
         (3248222580 : u32),
         (3835390401 : u32),
         (4022224774 : u32),
         (264347078 : u32),
         (604807628 : u32),
         (770255983 : u32),
         (1249150122 : u32),
         (1555081692 : u32),
         (1996064986 : u32),
         (2554220882 : u32),
         (2821834349 : u32),
         (2952996808 : u32),
         (3210313671 : u32),
         (3336571891 : u32),
         (3584528711 : u32),
         (113926993 : u32),
         (338241895 : u32),
         (666307205 : u32),
         (773529912 : u32),
         (1294757372 : u32),
         (1396182291 : u32),
         (1695183700 : u32),
         (1986661051 : u32),
         (2177026350 : u32),
         (2456956037 : u32),
         (2730485921 : u32),
         (2820302411 : u32),
         (3259730800 : u32),
         (3345764771 : u32),
         (3516065817 : u32),
         (3600352804 : u32),
         (4094571909 : u32),
         (275423344 : u32),
         (430227734 : u32),
         (506948616 : u32),
         (659060556 : u32),
         (883997877 : u32),
         (958139571 : u32),
         (1322822218 : u32),
         (1537002063 : u32),
         (1747873779 : u32),
         (1955562222 : u32),
         (2024104815 : u32),
         (2227730452 : u32),
         (2361852424 : u32),
         (2428436474 : u32),
         (2756734187 : u32),
         (3204031479 : u32),
         (3329325298 : u32)])
    (by rfl)

--  Initial hash values (first 32 bits of the fractional parts of the
--  square roots of the first 8 primes).
def HASH_INIT : (RustArray u32 8) :=
  RustM.of_isOk
    (do
    #v[(1779033703 : u32),
         (3144134277 : u32),
         (1013904242 : u32),
         (2773480762 : u32),
         (1359893119 : u32),
         (2600822924 : u32),
         (528734635 : u32),
         (1541459225 : u32)])
    (by rfl)

--  Ch(x, y, z) = (x AND y) XOR (NOT x AND z)
def ch (x : u32) (y : u32) (z : u32) : RustM u32 := do
  ((← (x &&&? y)) ^^^? (← ((← (Rust_primitives.Hax.Machine_int.not x)) &&&? z)))

--  Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z)
def maj (x : u32) (y : u32) (z : u32) : RustM u32 := do
  ((← ((← (x &&&? y)) ^^^? (← (x &&&? z)))) ^^^? (← (y &&&? z)))

--  lowercase sigma_0(x) = ROTR^7(x) XOR ROTR^18(x) XOR SHR^3(x)
def sigma0 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (7 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (18 : u32)))))
    ^^^? (← (x >>>? (3 : i32))))

--  lowercase sigma_1(x) = ROTR^17(x) XOR ROTR^19(x) XOR SHR^10(x)
def sigma1 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (17 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (19 : u32)))))
    ^^^? (← (x >>>? (10 : i32))))

--  uppercase Sigma_0(x) = ROTR^2(x) XOR ROTR^13(x) XOR ROTR^22(x)
def big_sigma0 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (2 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (13 : u32)))))
    ^^^? (← (Core_models.Num.Impl_8.rotate_right x (22 : u32))))

--  uppercase Sigma_1(x) = ROTR^6(x) XOR ROTR^11(x) XOR ROTR^25(x)
def big_sigma1 (x : u32) : RustM u32 := do
  ((← ((← (Core_models.Num.Impl_8.rotate_right x (6 : u32)))
      ^^^? (← (Core_models.Num.Impl_8.rotate_right x (11 : u32)))))
    ^^^? (← (Core_models.Num.Impl_8.rotate_right x (25 : u32))))

--  Expand a 64-byte block into a 64-word message schedule.
def schedule (block : (RustArray u8 64)) : RustM (RustArray u32 64) := do
  let w : (RustArray u32 64) ←
    (Rust_primitives.Hax.repeat (0 : u32) (64 : usize));
  let w : (RustArray u32 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun w _ => (do (pure true) : RustM Bool))
      w
      (fun w i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          w
          i
          (← (Core_models.Num.Impl_8.from_be_bytes
            #v[(← block[(← ((4 : usize) *? i))]_?),
                 (← block[(← ((← ((4 : usize) *? i)) +? (1 : usize)))]_?),
                 (← block[(← ((← ((4 : usize) *? i)) +? (2 : usize)))]_?),
                 (← block[(← ((← ((4 : usize) *? i)) +? (3 : usize)))]_?)]))) :
        RustM (RustArray u32 64))));
  let w : (RustArray u32 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (16 : usize)
      (64 : usize)
      (fun w _ => (do (pure true) : RustM Bool))
      w
      (fun w i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          w
          i
          (← (Core_models.Num.Impl_8.wrapping_add
            (← (Core_models.Num.Impl_8.wrapping_add
              (← (Core_models.Num.Impl_8.wrapping_add
                (← (sigma1 (← w[(← (i -? (2 : usize)))]_?)))
                (← w[(← (i -? (7 : usize)))]_?)))
              (← (sigma0 (← w[(← (i -? (15 : usize)))]_?)))))
            (← w[(← (i -? (16 : usize)))]_?)))) :
        RustM (RustArray u32 64))));
  (pure w)

--  Compress one 64-byte block into the running hash state.
def compress (block : (RustArray u8 64)) (h_in : (RustArray u32 8)) :
    RustM (RustArray u32 8) := do
  let w : (RustArray u32 64) ← (schedule block);
  let a : u32 ← h_in[(0 : usize)]_?;
  let b : u32 ← h_in[(1 : usize)]_?;
  let c : u32 ← h_in[(2 : usize)]_?;
  let d : u32 ← h_in[(3 : usize)]_?;
  let e : u32 ← h_in[(4 : usize)]_?;
  let f : u32 ← h_in[(5 : usize)]_?;
  let g : u32 ← h_in[(6 : usize)]_?;
  let h : u32 ← h_in[(7 : usize)]_?;
  let ⟨a, b, c, d, e, f, g, h⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (64 : usize)
      (fun ⟨a, b, c, d, e, f, g, h⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple8.mk a b c d e f g h)
      (fun ⟨a, b, c, d, e, f, g, h⟩ i =>
        (do
        let t1 : u32 ←
          (Core_models.Num.Impl_8.wrapping_add
            (← (Core_models.Num.Impl_8.wrapping_add
              (← (Core_models.Num.Impl_8.wrapping_add
                (← (Core_models.Num.Impl_8.wrapping_add h (← (big_sigma1 e))))
                (← (ch e f g))))
              (← K_TABLE[i]_?)))
            (← w[i]_?));
        let t2 : u32 ←
          (Core_models.Num.Impl_8.wrapping_add
            (← (big_sigma0 a))
            (← (maj a b c)));
        let h : u32 := g;
        let g : u32 := f;
        let f : u32 := e;
        let e : u32 ← (Core_models.Num.Impl_8.wrapping_add d t1);
        let d : u32 := c;
        let c : u32 := b;
        let b : u32 := a;
        let a : u32 ← (Core_models.Num.Impl_8.wrapping_add t1 t2);
        (pure (Rust_primitives.Hax.Tuple8.mk a b c d e f g h)) :
        RustM (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32))));
  (pure #v[(← (Core_models.Num.Impl_8.wrapping_add (← h_in[(0 : usize)]_?) a)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(1 : usize)]_?)
               b)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(2 : usize)]_?)
               c)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(3 : usize)]_?)
               d)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(4 : usize)]_?)
               e)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(5 : usize)]_?)
               f)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(6 : usize)]_?)
               g)),
             (← (Core_models.Num.Impl_8.wrapping_add
               (← h_in[(7 : usize)]_?)
               h))])

--  Compute SHA-256 of an arbitrary-length message.
-- 
--  Handles Merkle-Damgard padding: append bit `1`, then zeros, then the
--  64-bit big-endian bit length, so that the padded message length is a
--  multiple of 512 bits (64 bytes).
def sha256 (msg : (RustSlice u8)) : RustM (RustArray u8 32) := do
  let h : (RustArray u32 8) := HASH_INIT;
  let msg_len : usize ← (Core_models.Slice.Impl.len u8 msg);
  let bit_len : u64 ← ((← (Rust_primitives.Hax.cast_op msg_len)) *? (8 : u64));
  let num_full_blocks : usize ← (msg_len /? (64 : usize));
  let h : (RustArray u32 8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_full_blocks
      (fun h _ => (do (pure true) : RustM Bool))
      h
      (fun h i =>
        (do
        let block : (RustArray u8 64) ←
          (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
        let block : (RustArray u8 64) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (64 : usize)
            (fun block _ => (do (pure true) : RustM Bool))
            block
            (fun block j =>
              (do
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                block
                j
                (← msg[(← ((← (i *? (64 : usize))) +? j))]_?)) :
              RustM (RustArray u8 64))));
        let h : (RustArray u32 8) ← (compress block h);
        (pure h) :
        RustM (RustArray u32 8))));
  let remaining : usize ← (msg_len %? (64 : usize));
  let last_block : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let last_block : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      remaining
      (fun last_block _ => (do (pure true) : RustM Bool))
      last_block
      (fun last_block j =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          last_block
          j
          (← msg[(← ((← (num_full_blocks *? (64 : usize))) +? j))]_?)) :
        RustM (RustArray u8 64))));
  let last_block : (RustArray u8 64) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      last_block
      remaining
      (128 : u8));
  let ⟨h, last_block⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.lt remaining (56 : usize))) then
      let len_bytes : (RustArray u8 8) ←
        (Core_models.Num.Impl_9.to_be_bytes bit_len);
      let last_block : (RustArray u8 64) ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (8 : usize)
          (fun last_block _ => (do (pure true) : RustM Bool))
          last_block
          (fun last_block j =>
            (do
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              last_block
              (← ((56 : usize) +? j))
              (← len_bytes[j]_?)) :
            RustM (RustArray u8 64))));
      let h : (RustArray u32 8) ← (compress last_block h);
      (pure (Rust_primitives.Hax.Tuple2.mk h last_block))
    else
      let h : (RustArray u32 8) ← (compress last_block h);
      let pad_block : (RustArray u8 64) ←
        (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
      let len_bytes : (RustArray u8 8) ←
        (Core_models.Num.Impl_9.to_be_bytes bit_len);
      let pad_block : (RustArray u8 64) ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (8 : usize)
          (fun pad_block _ => (do (pure true) : RustM Bool))
          pad_block
          (fun pad_block j =>
            (do
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              pad_block
              (← ((56 : usize) +? j))
              (← len_bytes[j]_?)) :
            RustM (RustArray u8 64))));
      let h : (RustArray u32 8) ← (compress pad_block h);
      (pure (Rust_primitives.Hax.Tuple2.mk h last_block));
  let digest : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let digest : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun digest _ => (do (pure true) : RustM Bool))
      digest
      (fun digest i =>
        (do
        let bytes : (RustArray u8 4) ←
          (Core_models.Num.Impl_8.to_be_bytes (← h[i]_?));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((4 : usize) *? i))
            (← bytes[(0 : usize)]_?));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((← ((4 : usize) *? i)) +? (1 : usize)))
            (← bytes[(1 : usize)]_?));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((← ((4 : usize) *? i)) +? (2 : usize)))
            (← bytes[(2 : usize)]_?));
        let digest : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            digest
            (← ((← ((4 : usize) *? i)) +? (3 : usize)))
            (← bytes[(3 : usize)]_?));
        (pure digest) :
        RustM (RustArray u8 32))));
  (pure digest)

--  Fixed-length wrapper: SHA-256 on a 32-byte input.
def sha256_32 (msg : (RustArray u8 32)) : RustM (RustArray u8 32) := do
  (sha256 (← (Rust_primitives.unsize msg)))

end Libcrux_specs_hax.Sha256


namespace Libcrux_specs_hax.Sha512

--  SHA-512 round constants: first 64 bits of the fractional parts of the
--  cube roots of the first 80 primes (FIPS 180-4, Section 4.2.3).
def K_TABLE : (RustArray u64 80) :=
  RustM.of_isOk
    (do
    #v[(4794697086780616226 : u64),
         (8158064640168781261 : u64),
         (13096744586834688815 : u64),
         (16840607885511220156 : u64),
         (4131703408338449720 : u64),
         (6480981068601479193 : u64),
         (10538285296894168987 : u64),
         (12329834152419229976 : u64),
         (15566598209576043074 : u64),
         (1334009975649890238 : u64),
         (2608012711638119052 : u64),
         (6128411473006802146 : u64),
         (8268148722764581231 : u64),
         (9286055187155687089 : u64),
         (11230858885718282805 : u64),
         (13951009754708518548 : u64),
         (16472876342353939154 : u64),
         (17275323862435702243 : u64),
         (1135362057144423861 : u64),
         (2597628984639134821 : u64),
         (3308224258029322869 : u64),
         (5365058923640841347 : u64),
         (6679025012923562964 : u64),
         (8573033837759648693 : u64),
         (10970295158949994411 : u64),
         (12119686244451234320 : u64),
         (12683024718118986047 : u64),
         (13788192230050041572 : u64),
         (14330467153632333762 : u64),
         (15395433587784984357 : u64),
         (489312712824947311 : u64),
         (1452737877330783856 : u64),
         (2861767655752347644 : u64),
         (3322285676063803686 : u64),
         (5560940570517711597 : u64),
         (5996557281743188959 : u64),
         (7280758554555802590 : u64),
         (8532644243296465576 : u64),
         (9350256976987008742 : u64),
         (10552545826968843579 : u64),
         (11727347734174303076 : u64),
         (12113106623233404929 : u64),
         (14000437183269869457 : u64),
         (14369950271660146224 : u64),
         (15101387698204529176 : u64),
         (15463397548674623760 : u64),
         (17586052441742319658 : u64),
         (1182934255886127544 : u64),
         (1847814050463011016 : u64),
         (2177327727835720531 : u64),
         (2830643537854262169 : u64),
         (3796741975233480872 : u64),
         (4115178125766777443 : u64),
         (5681478168544905931 : u64),
         (6601373596472566643 : u64),
         (7507060721942968483 : u64),
         (8399075790359081724 : u64),
         (8693463985226723168 : u64),
         (9568029438360202098 : u64),
         (10144078919501101548 : u64),
         (10430055236837252648 : u64),
         (11840083180663258601 : u64),
         (13761210420658862357 : u64),
         (14299343276471374635 : u64),
         (14566680578165727644 : u64),
         (15097957966210449927 : u64),
         (16922976911328602910 : u64),
         (17689382322260857208 : u64),
         (500013540394364858 : u64),
         (748580250866718886 : u64),
         (1242879168328830382 : u64),
         (1977374033974150939 : u64),
         (2944078676154940804 : u64),
         (3659926193048069267 : u64),
         (4368137639120453308 : u64),
         (4836135668995329356 : u64),
         (5532061633213252278 : u64),
         (6448918945643986474 : u64),
         (6902733635092675308 : u64),
         (7801388544844847127 : u64)])
    (by rfl)

--  SHA-512 initial hash values: first 64 bits of the fractional parts of the
--  square roots of the first 8 primes (FIPS 180-4, Section 5.3.5).
def H512_INIT : (RustArray u64 8) :=
  RustM.of_isOk
    (do
    #v[(7640891576956012808 : u64),
         (13503953896175478587 : u64),
         (4354685564936845355 : u64),
         (11912009170470909681 : u64),
         (5840696475078001361 : u64),
         (11170449401992604703 : u64),
         (2270897969802886507 : u64),
         (6620516959819538809 : u64)])
    (by rfl)

--  SHA-384 initial hash values: first 64 bits of the fractional parts of the
--  square roots of the 9th through 16th primes (FIPS 180-4, Section 5.3.4).
def H384_INIT : (RustArray u64 8) :=
  RustM.of_isOk
    (do
    #v[(14680500436340154072 : u64),
         (7105036623409894663 : u64),
         (10473403895298186519 : u64),
         (1526699215303891257 : u64),
         (7436329637833083697 : u64),
         (10282925794625328401 : u64),
         (15784041429090275239 : u64),
         (5167115440072839076 : u64)])
    (by rfl)

--  Ch(x, y, z) = (x AND y) XOR (NOT x AND z) (FIPS 180-4, Section 4.1.3).
def ch (x : u64) (y : u64) (z : u64) : RustM u64 := do
  ((← (x &&&? y)) ^^^? (← ((← (Rust_primitives.Hax.Machine_int.not x)) &&&? z)))

--  Maj(x, y, z) = (x AND y) XOR (x AND z) XOR (y AND z) (FIPS 180-4, Section 4.1.3).
def maj (x : u64) (y : u64) (z : u64) : RustM u64 := do
  ((← ((← (x &&&? y)) ^^^? (← (x &&&? z)))) ^^^? (← (y &&&? z)))

--  Big Sigma 0: ROTR^28(x) XOR ROTR^34(x) XOR ROTR^39(x) (FIPS 180-4, Section 4.1.3).
def big_sigma0 (x : u64) : RustM u64 := do
  ((← ((← (Core_models.Num.Impl_9.rotate_right x (28 : u32)))
      ^^^? (← (Core_models.Num.Impl_9.rotate_right x (34 : u32)))))
    ^^^? (← (Core_models.Num.Impl_9.rotate_right x (39 : u32))))

--  Big Sigma 1: ROTR^14(x) XOR ROTR^18(x) XOR ROTR^41(x) (FIPS 180-4, Section 4.1.3).
def big_sigma1 (x : u64) : RustM u64 := do
  ((← ((← (Core_models.Num.Impl_9.rotate_right x (14 : u32)))
      ^^^? (← (Core_models.Num.Impl_9.rotate_right x (18 : u32)))))
    ^^^? (← (Core_models.Num.Impl_9.rotate_right x (41 : u32))))

--  Small sigma 0: ROTR^1(x) XOR ROTR^8(x) XOR SHR^7(x) (FIPS 180-4, Section 4.1.3).
def sigma0 (x : u64) : RustM u64 := do
  ((← ((← (Core_models.Num.Impl_9.rotate_right x (1 : u32)))
      ^^^? (← (Core_models.Num.Impl_9.rotate_right x (8 : u32)))))
    ^^^? (← (x >>>? (7 : i32))))

--  Small sigma 1: ROTR^19(x) XOR ROTR^61(x) XOR SHR^6(x) (FIPS 180-4, Section 4.1.3).
def sigma1 (x : u64) : RustM u64 := do
  ((← ((← (Core_models.Num.Impl_9.rotate_right x (19 : u32)))
      ^^^? (← (Core_models.Num.Impl_9.rotate_right x (61 : u32)))))
    ^^^? (← (x >>>? (6 : i32))))

--  Prepare the 80-word message schedule from a 128-byte block (FIPS 180-4, Section 6.4.2).
-- 
--  Words 0..15 are parsed as big-endian u64 from the block.
--  Words 16..79 are computed: W_t = sigma1(W_{t-2}) + W_{t-7} + sigma0(W_{t-15}) + W_{t-16}.
def schedule (block : (RustArray u8 128)) : RustM (RustArray u64 80) := do
  let w : (RustArray u64 80) ←
    (Rust_primitives.Hax.repeat (0 : u64) (80 : usize));
  let i : usize := (0 : usize);
  let ⟨i, w⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, w⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (16 : usize)) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i w)
      (fun ⟨i, w⟩ =>
        (do
        let base : usize ← (i *? (8 : usize));
        let w : (RustArray u64 80) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            i
            (← (Rust_primitives.Hax.Machine_int.bitor
              (← (Rust_primitives.Hax.Machine_int.bitor
                (← (Rust_primitives.Hax.Machine_int.bitor
                  (← (Rust_primitives.Hax.Machine_int.bitor
                    (← (Rust_primitives.Hax.Machine_int.bitor
                      (← (Rust_primitives.Hax.Machine_int.bitor
                        (← (Rust_primitives.Hax.Machine_int.bitor
                          (← ((← (Rust_primitives.Hax.cast_op
                              (← block[base]_?)))
                            <<<? (56 : i32)))
                          (← ((← (Rust_primitives.Hax.cast_op
                              (← block[(← (base +? (1 : usize)))]_?)))
                            <<<? (48 : i32)))))
                        (← ((← (Rust_primitives.Hax.cast_op
                            (← block[(← (base +? (2 : usize)))]_?)))
                          <<<? (40 : i32)))))
                      (← ((← (Rust_primitives.Hax.cast_op
                          (← block[(← (base +? (3 : usize)))]_?)))
                        <<<? (32 : i32)))))
                    (← ((← (Rust_primitives.Hax.cast_op
                        (← block[(← (base +? (4 : usize)))]_?)))
                      <<<? (24 : i32)))))
                  (← ((← (Rust_primitives.Hax.cast_op
                      (← block[(← (base +? (5 : usize)))]_?)))
                    <<<? (16 : i32)))))
                (← ((← (Rust_primitives.Hax.cast_op
                    (← block[(← (base +? (6 : usize)))]_?)))
                  <<<? (8 : i32)))))
              (← (Rust_primitives.Hax.cast_op
                (← block[(← (base +? (7 : usize)))]_?))))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i w)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 80)))));
  let ⟨i, w⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, w⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (80 : usize)) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i w)
      (fun ⟨i, w⟩ =>
        (do
        let w : (RustArray u64 80) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            i
            (← (Core_models.Num.Impl_9.wrapping_add
              (← (Core_models.Num.Impl_9.wrapping_add
                (← (Core_models.Num.Impl_9.wrapping_add
                  (← (sigma1 (← w[(← (i -? (2 : usize)))]_?)))
                  (← w[(← (i -? (7 : usize)))]_?)))
                (← (sigma0 (← w[(← (i -? (15 : usize)))]_?)))))
              (← w[(← (i -? (16 : usize)))]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i w)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 80)))));
  (pure w)

--  Compress one 128-byte block into the hash state (FIPS 180-4, Section 6.4.2).
def compress (block : (RustArray u8 128)) (h : (RustArray u64 8)) :
    RustM (RustArray u64 8) := do
  let w : (RustArray u64 80) ← (schedule block);
  let a : u64 ← h[(0 : usize)]_?;
  let b : u64 ← h[(1 : usize)]_?;
  let c : u64 ← h[(2 : usize)]_?;
  let d : u64 ← h[(3 : usize)]_?;
  let e : u64 ← h[(4 : usize)]_?;
  let f : u64 ← h[(5 : usize)]_?;
  let g : u64 ← h[(6 : usize)]_?;
  let hh : u64 ← h[(7 : usize)]_?;
  let t : usize := (0 : usize);
  let ⟨a, b, c, d, e, f, g, hh, t⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨a, b, c, d, e, f, g, hh, t⟩ => (do (pure true) : RustM Bool))
      (fun ⟨a, b, c, d, e, f, g, hh, t⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt t (80 : usize)) : RustM Bool))
      (fun ⟨a, b, c, d, e, f, g, hh, t⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple9.mk a b c d e f g hh t)
      (fun ⟨a, b, c, d, e, f, g, hh, t⟩ =>
        (do
        let t1 : u64 ←
          (Core_models.Num.Impl_9.wrapping_add
            (← (Core_models.Num.Impl_9.wrapping_add
              (← (Core_models.Num.Impl_9.wrapping_add
                (← (Core_models.Num.Impl_9.wrapping_add hh (← (big_sigma1 e))))
                (← (ch e f g))))
              (← K_TABLE[t]_?)))
            (← w[t]_?));
        let t2 : u64 ←
          (Core_models.Num.Impl_9.wrapping_add
            (← (big_sigma0 a))
            (← (maj a b c)));
        let hh : u64 := g;
        let g : u64 := f;
        let f : u64 := e;
        let e : u64 ← (Core_models.Num.Impl_9.wrapping_add d t1);
        let d : u64 := c;
        let c : u64 := b;
        let b : u64 := a;
        let a : u64 ← (Core_models.Num.Impl_9.wrapping_add t1 t2);
        let t : usize ← (t +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple9.mk a b c d e f g hh t)) :
        RustM
        (Rust_primitives.Hax.Tuple9 u64 u64 u64 u64 u64 u64 u64 u64 usize))));
  (pure #v[(← (Core_models.Num.Impl_9.wrapping_add (← h[(0 : usize)]_?) a)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(1 : usize)]_?) b)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(2 : usize)]_?) c)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(3 : usize)]_?) d)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(4 : usize)]_?) e)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(5 : usize)]_?) f)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(6 : usize)]_?) g)),
             (← (Core_models.Num.Impl_9.wrapping_add (← h[(7 : usize)]_?) hh))])

--  SHA-512 hash (FIPS 180-4, Section 6.4).
-- 
--  Pads the message to a multiple of 128 bytes (1024 bits) using
--  Merkle-Damgard strengthening with a 128-bit big-endian length field.
def sha512 (msg : (RustSlice u8)) : RustM (RustArray u8 64) := do
  let h : (RustArray u64 8) := H512_INIT;
  let msg_len : usize ← (Core_models.Slice.Impl.len u8 msg);
  let bit_len : u128 ←
    ((← (Rust_primitives.Hax.cast_op msg_len)) *? (8 : u128));
  let offset : usize := (0 : usize);
  let ⟨h, offset⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨h, offset⟩ => (do (pure true) : RustM Bool))
      (fun ⟨h, offset⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.le
          (← (offset +? (128 : usize)))
          msg_len) :
        RustM Bool))
      (fun ⟨h, offset⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk h offset)
      (fun ⟨h, offset⟩ =>
        (do
        let block : (RustArray u8 128) ←
          (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
        let i : usize := (0 : usize);
        let ⟨block, i⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨block, i⟩ => (do (pure true) : RustM Bool))
            (fun ⟨block, i⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt i (128 : usize)) :
              RustM Bool))
            (fun ⟨block, i⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk block i)
            (fun ⟨block, i⟩ =>
              (do
              let block : (RustArray u8 128) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  block
                  i
                  (← msg[(← (offset +? i))]_?));
              let i : usize ← (i +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk block i)) :
              RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) usize))));
        let h : (RustArray u64 8) ← (compress block h);
        let offset : usize ← (offset +? (128 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk h offset)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 8) usize))));
  let remaining : usize ← (msg_len -? offset);
  let block : (RustArray u8 128) ←
    (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
  let i : usize := (0 : usize);
  let ⟨block, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨block, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨block, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i remaining) : RustM Bool))
      (fun ⟨block, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk block i)
      (fun ⟨block, i⟩ =>
        (do
        let block : (RustArray u8 128) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            block
            i
            (← msg[(← (offset +? i))]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk block i)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) usize))));
  let block : (RustArray u8 128) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      block
      remaining
      (128 : u8));
  let ⟨block, h⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.ge remaining (112 : usize))) then
      let h : (RustArray u64 8) ← (compress block h);
      let block : (RustArray u8 128) ←
        (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
      (pure (Rust_primitives.Hax.Tuple2.mk block h))
    else
      (pure (Rust_primitives.Hax.Tuple2.mk block h));
  let len_bytes : (RustArray u8 16) ←
    (Core_models.Num.Impl_10.to_be_bytes bit_len);
  let j : usize := (0 : usize);
  let ⟨block, j⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨block, j⟩ => (do (pure true) : RustM Bool))
      (fun ⟨block, j⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt j (16 : usize)) : RustM Bool))
      (fun ⟨block, j⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk block j)
      (fun ⟨block, j⟩ =>
        (do
        let block : (RustArray u8 128) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            block
            (← ((112 : usize) +? j))
            (← len_bytes[j]_?));
        let j : usize ← (j +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk block j)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) usize))));
  let h : (RustArray u64 8) ← (compress block h);
  let output : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let k : usize := (0 : usize);
  let ⟨k, output⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨k, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨k, output⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (8 : usize)) : RustM Bool))
      (fun ⟨k, output⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk k output)
      (fun ⟨k, output⟩ =>
        (do
        let bytes : (RustArray u8 8) ←
          (Core_models.Num.Impl_9.to_be_bytes (← h[k]_?));
        let b : usize := (0 : usize);
        let ⟨b, output⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨b, output⟩ => (do (pure true) : RustM Bool))
            (fun ⟨b, output⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt b (8 : usize)) : RustM Bool))
            (fun ⟨b, output⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk b output)
            (fun ⟨b, output⟩ =>
              (do
              let output : (RustArray u8 64) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  output
                  (← ((← (k *? (8 : usize))) +? b))
                  (← bytes[b]_?));
              let b : usize ← (b +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk b output)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 64)))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk k output)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 64)))));
  (pure output)

--  SHA-384 hash (FIPS 180-4, Section 6.5).
-- 
--  Same algorithm as SHA-512 but with a different initial hash value
--  and the output truncated to 48 bytes (384 bits).
def sha384 (msg : (RustSlice u8)) : RustM (RustArray u8 48) := do
  let h : (RustArray u64 8) := H384_INIT;
  let msg_len : usize ← (Core_models.Slice.Impl.len u8 msg);
  let bit_len : u128 ←
    ((← (Rust_primitives.Hax.cast_op msg_len)) *? (8 : u128));
  let offset : usize := (0 : usize);
  let ⟨h, offset⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨h, offset⟩ => (do (pure true) : RustM Bool))
      (fun ⟨h, offset⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.le
          (← (offset +? (128 : usize)))
          msg_len) :
        RustM Bool))
      (fun ⟨h, offset⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk h offset)
      (fun ⟨h, offset⟩ =>
        (do
        let block : (RustArray u8 128) ←
          (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
        let i : usize := (0 : usize);
        let ⟨block, i⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨block, i⟩ => (do (pure true) : RustM Bool))
            (fun ⟨block, i⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt i (128 : usize)) :
              RustM Bool))
            (fun ⟨block, i⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk block i)
            (fun ⟨block, i⟩ =>
              (do
              let block : (RustArray u8 128) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  block
                  i
                  (← msg[(← (offset +? i))]_?));
              let i : usize ← (i +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk block i)) :
              RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) usize))));
        let h : (RustArray u64 8) ← (compress block h);
        let offset : usize ← (offset +? (128 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk h offset)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 8) usize))));
  let remaining : usize ← (msg_len -? offset);
  let block : (RustArray u8 128) ←
    (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
  let i : usize := (0 : usize);
  let ⟨block, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨block, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨block, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i remaining) : RustM Bool))
      (fun ⟨block, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk block i)
      (fun ⟨block, i⟩ =>
        (do
        let block : (RustArray u8 128) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            block
            i
            (← msg[(← (offset +? i))]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk block i)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) usize))));
  let block : (RustArray u8 128) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      block
      remaining
      (128 : u8));
  let ⟨block, h⟩ ←
    if (← (Rust_primitives.Hax.Machine_int.ge remaining (112 : usize))) then
      let h : (RustArray u64 8) ← (compress block h);
      let block : (RustArray u8 128) ←
        (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
      (pure (Rust_primitives.Hax.Tuple2.mk block h))
    else
      (pure (Rust_primitives.Hax.Tuple2.mk block h));
  let len_bytes : (RustArray u8 16) ←
    (Core_models.Num.Impl_10.to_be_bytes bit_len);
  let j : usize := (0 : usize);
  let ⟨block, j⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨block, j⟩ => (do (pure true) : RustM Bool))
      (fun ⟨block, j⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt j (16 : usize)) : RustM Bool))
      (fun ⟨block, j⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk block j)
      (fun ⟨block, j⟩ =>
        (do
        let block : (RustArray u8 128) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            block
            (← ((112 : usize) +? j))
            (← len_bytes[j]_?));
        let j : usize ← (j +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk block j)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 128) usize))));
  let h : (RustArray u64 8) ← (compress block h);
  let output : (RustArray u8 48) ←
    (Rust_primitives.Hax.repeat (0 : u8) (48 : usize));
  let k : usize := (0 : usize);
  let ⟨k, output⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨k, output⟩ => (do (pure true) : RustM Bool))
      (fun ⟨k, output⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (6 : usize)) : RustM Bool))
      (fun ⟨k, output⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk k output)
      (fun ⟨k, output⟩ =>
        (do
        let bytes : (RustArray u8 8) ←
          (Core_models.Num.Impl_9.to_be_bytes (← h[k]_?));
        let b : usize := (0 : usize);
        let ⟨b, output⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨b, output⟩ => (do (pure true) : RustM Bool))
            (fun ⟨b, output⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt b (8 : usize)) : RustM Bool))
            (fun ⟨b, output⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk b output)
            (fun ⟨b, output⟩ =>
              (do
              let output : (RustArray u8 48) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  output
                  (← ((← (k *? (8 : usize))) +? b))
                  (← bytes[b]_?));
              let b : usize ← (b +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk b output)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 48)))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk k output)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 48)))));
  (pure output)

end Libcrux_specs_hax.Sha512


namespace Libcrux_specs_hax.Sha3

--  Keccak round constants (FIPS 202, Section 3.2.5).
def RC : (RustArray u64 24) :=
  RustM.of_isOk
    (do
    #v[(1 : u64),
         (32898 : u64),
         (9223372036854808714 : u64),
         (9223372039002292224 : u64),
         (32907 : u64),
         (2147483649 : u64),
         (9223372039002292353 : u64),
         (9223372036854808585 : u64),
         (138 : u64),
         (136 : u64),
         (2147516425 : u64),
         (2147483658 : u64),
         (2147516555 : u64),
         (9223372036854775947 : u64),
         (9223372036854808713 : u64),
         (9223372036854808579 : u64),
         (9223372036854808578 : u64),
         (9223372036854775936 : u64),
         (32778 : u64),
         (9223372039002259466 : u64),
         (9223372039002292353 : u64),
         (9223372036854808704 : u64),
         (2147483649 : u64),
         (9223372039002292232 : u64)])
    (by rfl)

--  Rotation offsets for the rho step (FIPS 202, Table 2).
--  Indexed as `x + 5*y` where `(x,y)` is the lane coordinate.
def ROT_OFFSETS : (RustArray u32 25) :=
  RustM.of_isOk
    (do
    #v[(0 : u32),
         (1 : u32),
         (62 : u32),
         (28 : u32),
         (27 : u32),
         (36 : u32),
         (44 : u32),
         (6 : u32),
         (55 : u32),
         (20 : u32),
         (3 : u32),
         (10 : u32),
         (43 : u32),
         (25 : u32),
         (39 : u32),
         (41 : u32),
         (45 : u32),
         (15 : u32),
         (21 : u32),
         (8 : u32),
         (18 : u32),
         (2 : u32),
         (61 : u32),
         (56 : u32),
         (14 : u32)])
    (by rfl)

--  Rotate a u64 left by `n` bits.
def rotl64 (x : u64) (n : u32) : RustM u64 := do
  if
  (← ((← (Rust_primitives.Hax.Machine_int.eq n (0 : u32)))
    ||? (← (Rust_primitives.Hax.Machine_int.eq n (64 : u32))))) then
    (pure x)
  else
    (Rust_primitives.Hax.Machine_int.bitor
      (← (x <<<? n))
      (← (x >>>? (← ((64 : u32) -? n)))))

--  Theta step: column parity diffusion (FIPS 202, Section 3.2.1).
def theta (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let c : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let x : usize := (0 : usize);
  let ⟨c, x⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨c, x⟩ => (do (pure true) : RustM Bool))
      (fun ⟨c, x⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt x (5 : usize)) : RustM Bool))
      (fun ⟨c, x⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk c x)
      (fun ⟨c, x⟩ =>
        (do
        let c : (RustArray u64 5) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            c
            x
            (← ((← ((← ((← ((← state[x]_?)
                    ^^^? (← state[(← (x +? (5 : usize)))]_?)))
                  ^^^? (← state[(← (x +? (10 : usize)))]_?)))
                ^^^? (← state[(← (x +? (15 : usize)))]_?)))
              ^^^? (← state[(← (x +? (20 : usize)))]_?))));
        let x : usize ← (x +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk c x)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 5) usize))));
  let d : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let x : usize := (0 : usize);
  let ⟨d, x⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨d, x⟩ => (do (pure true) : RustM Bool))
      (fun ⟨d, x⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt x (5 : usize)) : RustM Bool))
      (fun ⟨d, x⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk d x)
      (fun ⟨d, x⟩ =>
        (do
        let d : (RustArray u64 5) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            d
            x
            (← ((← c[(← ((← (x +? (4 : usize))) %? (5 : usize)))]_?)
              ^^^? (← (rotl64
                (← c[(← ((← (x +? (1 : usize))) %? (5 : usize)))]_?)
                (1 : u32))))));
        let x : usize ← (x +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk d x)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 5) usize))));
  let result : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (25 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u64 25) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← ((← state[i]_?) ^^^? (← d[(← (i %? (5 : usize)))]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
  (pure result)

--  Rho step: bitwise rotation (FIPS 202, Section 3.2.2).
def rho (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let result : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (25 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u64 25) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← (rotl64 (← state[i]_?) (← ROT_OFFSETS[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
  (pure result)

--  Pi step: lane transposition (FIPS 202, Section 3.2.3).
--  `A'[x, y] = A[(x + 3y) mod 5, x]`.
def pi (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let result : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let y : usize := (0 : usize);
  let ⟨result, y⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨result, y⟩ => (do (pure true) : RustM Bool))
      (fun ⟨result, y⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt y (5 : usize)) : RustM Bool))
      (fun ⟨result, y⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk result y)
      (fun ⟨result, y⟩ =>
        (do
        let x : usize := (0 : usize);
        let ⟨result, x⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨result, x⟩ => (do (pure true) : RustM Bool))
            (fun ⟨result, x⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt x (5 : usize)) : RustM Bool))
            (fun ⟨result, x⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk result x)
            (fun ⟨result, x⟩ =>
              (do
              let result : (RustArray u64 25) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  result
                  (← (x +? (← ((5 : usize) *? y))))
                  (← state[
                    (← ((← ((← (x +? (← ((3 : usize) *? y)))) %? (5 : usize)))
                      +? (← ((5 : usize) *? x))))
                    ]_?));
              let x : usize ← (x +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk result x)) :
              RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 25) usize))));
        let y : usize ← (y +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk result y)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 25) usize))));
  (pure result)

--  Chi step: non-linear row mixing (FIPS 202, Section 3.2.4).
def chi (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let result : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let y : usize := (0 : usize);
  let ⟨result, y⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨result, y⟩ => (do (pure true) : RustM Bool))
      (fun ⟨result, y⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt y (5 : usize)) : RustM Bool))
      (fun ⟨result, y⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk result y)
      (fun ⟨result, y⟩ =>
        (do
        let x : usize := (0 : usize);
        let ⟨result, x⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨result, x⟩ => (do (pure true) : RustM Bool))
            (fun ⟨result, x⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt x (5 : usize)) : RustM Bool))
            (fun ⟨result, x⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk result x)
            (fun ⟨result, x⟩ =>
              (do
              let result : (RustArray u64 25) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  result
                  (← (x +? (← ((5 : usize) *? y))))
                  (← ((← state[(← (x +? (← ((5 : usize) *? y))))]_?)
                    ^^^? (← ((← (Rust_primitives.Hax.Machine_int.not
                        (← state[
                          (← ((← ((← (x +? (1 : usize))) %? (5 : usize)))
                            +? (← ((5 : usize) *? y))))
                          ]_?)))
                      &&&? (← state[
                        (← ((← ((← (x +? (2 : usize))) %? (5 : usize)))
                          +? (← ((5 : usize) *? y))))
                        ]_?))))));
              let x : usize ← (x +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk result x)) :
              RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 25) usize))));
        let y : usize ← (y +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk result y)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 25) usize))));
  (pure result)

--  Iota step: round constant addition (FIPS 202, Section 3.2.5).
def iota (state : (RustArray u64 25)) (round : usize) :
    RustM (RustArray u64 25) := do
  let result : (RustArray u64 25) := state;
  let result : (RustArray u64 25) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (0 : usize)
      (← ((← result[(0 : usize)]_?) ^^^? (← RC[round]_?))));
  (pure result)

--  Keccak-f[1600] permutation: 24 rounds of theta, rho, pi, chi, iota.
def keccak_f1600 (state : (RustArray u64 25)) : RustM (RustArray u64 25) := do
  let s : (RustArray u64 25) := state;
  let round : usize := (0 : usize);
  let ⟨round, s⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨round, s⟩ => (do (pure true) : RustM Bool))
      (fun ⟨round, s⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt round (24 : usize)) : RustM Bool))
      (fun ⟨round, s⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk round s)
      (fun ⟨round, s⟩ =>
        (do
        let s : (RustArray u64 25) ← (theta s);
        let s : (RustArray u64 25) ← (rho s);
        let s : (RustArray u64 25) ← (pi s);
        let s : (RustArray u64 25) ← (chi s);
        let s : (RustArray u64 25) ← (iota s round);
        let round : usize ← (round +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk round s)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
  (pure s)

--  Convert a byte slice (up to 200 bytes) to the Keccak u64 lane array.
-- 
--  Lanes are in `x + 5*y` order. Byte order within each lane is little-endian.
--  Bytes beyond the slice length are treated as zero.
def bytes_to_state (bytes : (RustSlice u8)) : RustM (RustArray u64 25) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let i : usize := (0 : usize);
  let ⟨i, state⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, state⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, state⟩ =>
        (do
        ((← (Rust_primitives.Hax.Machine_int.lt i (25 : usize)))
          &&? (← (Rust_primitives.Hax.Machine_int.lt
            (← (i *? (8 : usize)))
            (← (Core_models.Slice.Impl.len u8 bytes))))) :
        RustM Bool))
      (fun ⟨i, state⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i state)
      (fun ⟨i, state⟩ =>
        (do
        let lane : u64 := (0 : u64);
        let j : usize := (0 : usize);
        let ⟨j, lane⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, lane⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, lane⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, lane⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j lane)
            (fun ⟨j, lane⟩ =>
              (do
              let lane : u64 ←
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← ((← (i *? (8 : usize))) +? j))
                  (← (Core_models.Slice.Impl.len u8 bytes)))) then
                  let lane : u64 ←
                    (Rust_primitives.Hax.Machine_int.bitor
                      lane
                      (← ((← (Rust_primitives.Hax.cast_op
                          (← bytes[(← ((← (i *? (8 : usize))) +? j))]_?)))
                        <<<? (← (j *? (8 : usize))))));
                  (pure lane)
                else
                  (pure lane);
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j lane)) :
              RustM (Rust_primitives.Hax.Tuple2 usize u64))));
        let state : (RustArray u64 25) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            state
            i
            lane);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i state)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
  (pure state)

--  Convert the Keccak u64 lane array back to 200 bytes (little-endian).
def state_to_bytes (state : (RustArray u64 25)) : RustM (RustArray u8 200) := do
  let bytes : (RustArray u8 200) ←
    (Rust_primitives.Hax.repeat (0 : u8) (200 : usize));
  let i : usize := (0 : usize);
  let ⟨bytes, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨bytes, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨bytes, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (25 : usize)) : RustM Bool))
      (fun ⟨bytes, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk bytes i)
      (fun ⟨bytes, i⟩ =>
        (do
        let j : usize := (0 : usize);
        let ⟨bytes, j⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨bytes, j⟩ => (do (pure true) : RustM Bool))
            (fun ⟨bytes, j⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨bytes, j⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk bytes j)
            (fun ⟨bytes, j⟩ =>
              (do
              let bytes : (RustArray u8 200) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  bytes
                  (← ((← (i *? (8 : usize))) +? j))
                  (← (Rust_primitives.Hax.cast_op
                    (← ((← state[i]_?) >>>? (← (j *? (8 : usize))))))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk bytes j)) :
              RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 200) usize))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk bytes i)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 200) usize))));
  (pure bytes)

--  XOR a byte into the Keccak state at byte position `pos`.
-- 
--  Position `pos` maps to lane `pos / 8`, byte offset `pos % 8` (little-endian).
def xor_byte_into_state (state : (RustArray u64 25)) (pos : usize) (byte : u8) :
    RustM (RustArray u64 25) := do
  let lane : usize ← (pos /? (8 : usize));
  let offset : usize ← (pos %? (8 : usize));
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      lane
      (← ((← state[lane]_?)
        ^^^? (← ((← (Rust_primitives.Hax.cast_op byte))
          <<<? (← (offset *? (8 : usize))))))));
  (pure state)

--  Keccak sponge absorb phase.
-- 
--  Absorbs `data` into `state` at the given `rate` (in bytes), using `domain_sep`
--  as the domain separation byte. Applies multi-rate padding (FIPS 202, Section 5.1):
--    - XOR `domain_sep` at position `len(data) mod rate`
--    - XOR `0x80` at position `rate - 1`
-- 
--  Returns the state after absorption and final permutation.
def keccak_absorb
    (state : (RustArray u64 25))
    (rate : usize)
    (data : (RustSlice u8))
    (domain_sep : u8) :
    RustM (RustArray u64 25) := do
  let s : (RustArray u64 25) := state;
  let offset : usize := (0 : usize);
  let ⟨offset, s⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨offset, s⟩ => (do (pure true) : RustM Bool))
      (fun ⟨offset, s⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.le
          (← (offset +? rate))
          (← (Core_models.Slice.Impl.len u8 data))) :
        RustM Bool))
      (fun ⟨offset, s⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk offset s)
      (fun ⟨offset, s⟩ =>
        (do
        let i : usize := (0 : usize);
        let ⟨i, s⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨i, s⟩ => (do (pure true) : RustM Bool))
            (fun ⟨i, s⟩ =>
              (do (Rust_primitives.Hax.Machine_int.lt i rate) : RustM Bool))
            (fun ⟨i, s⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk i s)
            (fun ⟨i, s⟩ =>
              (do
              let s : (RustArray u64 25) ←
                (xor_byte_into_state s i (← data[(← (offset +? i))]_?));
              let i : usize ← (i +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk i s)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
        let s : (RustArray u64 25) ← (keccak_f1600 s);
        let offset : usize ← (offset +? rate);
        (pure (Rust_primitives.Hax.Tuple2.mk offset s)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
  let remaining : usize ← ((← (Core_models.Slice.Impl.len u8 data)) -? offset);
  let i : usize := (0 : usize);
  let ⟨i, s⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, s⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, s⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i remaining) : RustM Bool))
      (fun ⟨i, s⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i s)
      (fun ⟨i, s⟩ =>
        (do
        let s : (RustArray u64 25) ←
          (xor_byte_into_state s i (← data[(← (offset +? i))]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i s)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 25)))));
  let s : (RustArray u64 25) ← (xor_byte_into_state s remaining domain_sep);
  let s : (RustArray u64 25) ←
    (xor_byte_into_state s (← (rate -? (1 : usize))) (128 : u8));
  let s : (RustArray u64 25) ← (keccak_f1600 s);
  (pure s)

--  Keccak sponge squeeze phase.
-- 
--  Extracts `output_len` bytes from the sponge state, permuting between
--  rate-sized output blocks as needed.
def keccak_squeeze
    (state : (RustArray u64 25))
    (rate : usize)
    (output_len : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let s : (RustArray u64 25) := state;
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8 output_len);
  let squeezed : usize := (0 : usize);
  let ⟨output, s, squeezed⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨output, s, squeezed⟩ => (do (pure true) : RustM Bool))
      (fun ⟨output, s, squeezed⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt squeezed output_len) : RustM Bool))
      (fun ⟨output, s, squeezed⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk output s squeezed)
      (fun ⟨output, s, squeezed⟩ =>
        (do
        let block : (RustArray u8 200) ← (state_to_bytes s);
        let available : usize ←
          if
          (← (Rust_primitives.Hax.Machine_int.lt
            (← (output_len -? squeezed))
            rate)) then
            (output_len -? squeezed)
          else
            (pure rate);
        let i : usize := (0 : usize);
        let ⟨i, output⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨i, output⟩ => (do (pure true) : RustM Bool))
            (fun ⟨i, output⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt i available) : RustM Bool))
            (fun ⟨i, output⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk i output)
            (fun ⟨i, output⟩ =>
              (do
              let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                  output
                  (← block[i]_?));
              let i : usize ← (i +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk i output)) :
              RustM
              (Rust_primitives.Hax.Tuple2
                usize
                (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
        let squeezed : usize ← (squeezed +? available);
        if (← (Rust_primitives.Hax.Machine_int.lt squeezed output_len)) then
          let s : (RustArray u64 25) ← (keccak_f1600 s);
          (pure (Rust_primitives.Hax.Tuple3.mk output s squeezed))
        else
          (pure (Rust_primitives.Hax.Tuple3.mk output s squeezed)) :
        RustM
        (Rust_primitives.Hax.Tuple3
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
          (RustArray u64 25)
          usize))));
  (pure output)

--  SHA3-224: 224-bit hash. Rate = 144 bytes, domain separation = 0x06.
def sha3_224 (msg : (RustSlice u8)) : RustM (RustArray u8 28) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let state : (RustArray u64 25) ←
    (keccak_absorb state (144 : usize) msg (6 : u8));
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (keccak_squeeze state (144 : usize) (28 : usize));
  let result : (RustArray u8 28) ←
    (Rust_primitives.Hax.repeat (0 : u8) (28 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (28 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u8 28) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← output[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 28)))));
  (pure result)

--  SHA3-256: 256-bit hash. Rate = 136 bytes, domain separation = 0x06.
def sha3_256 (msg : (RustSlice u8)) : RustM (RustArray u8 32) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let state : (RustArray u64 25) ←
    (keccak_absorb state (136 : usize) msg (6 : u8));
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (keccak_squeeze state (136 : usize) (32 : usize));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← output[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  (pure result)

--  SHA3-384: 384-bit hash. Rate = 104 bytes, domain separation = 0x06.
def sha3_384 (msg : (RustSlice u8)) : RustM (RustArray u8 48) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let state : (RustArray u64 25) ←
    (keccak_absorb state (104 : usize) msg (6 : u8));
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (keccak_squeeze state (104 : usize) (48 : usize));
  let result : (RustArray u8 48) ←
    (Rust_primitives.Hax.repeat (0 : u8) (48 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (48 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u8 48) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← output[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 48)))));
  (pure result)

--  SHA3-512: 512-bit hash. Rate = 72 bytes, domain separation = 0x06.
def sha3_512 (msg : (RustSlice u8)) : RustM (RustArray u8 64) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let state : (RustArray u64 25) ←
    (keccak_absorb state (72 : usize) msg (6 : u8));
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (keccak_squeeze state (72 : usize) (64 : usize));
  let result : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (64 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u8 64) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← output[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 64)))));
  (pure result)

--  SHAKE128: extendable-output function. Rate = 168 bytes, domain separation = 0x1F.
def shake128 (msg : (RustSlice u8)) (output_len : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let state : (RustArray u64 25) ←
    (keccak_absorb state (168 : usize) msg (31 : u8));
  (keccak_squeeze state (168 : usize) output_len)

--  SHAKE256: extendable-output function. Rate = 136 bytes, domain separation = 0x1F.
def shake256 (msg : (RustSlice u8)) (output_len : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let state : (RustArray u64 25) ←
    (Rust_primitives.Hax.repeat (0 : u64) (25 : usize));
  let state : (RustArray u64 25) ←
    (keccak_absorb state (136 : usize) msg (31 : u8));
  (keccak_squeeze state (136 : usize) output_len)

end Libcrux_specs_hax.Sha3


namespace Libcrux_specs_hax.Blake2

--  Message schedule permutation table (10 standard permutations from RFC 7693).
def SIGMA : (RustArray (RustArray usize 16) 10) :=
  RustM.of_isOk
    (do
    #v[#v[(0 : usize),
            (1 : usize),
            (2 : usize),
            (3 : usize),
            (4 : usize),
            (5 : usize),
            (6 : usize),
            (7 : usize),
            (8 : usize),
            (9 : usize),
            (10 : usize),
            (11 : usize),
            (12 : usize),
            (13 : usize),
            (14 : usize),
            (15 : usize)],
         #v[(14 : usize),
              (10 : usize),
              (4 : usize),
              (8 : usize),
              (9 : usize),
              (15 : usize),
              (13 : usize),
              (6 : usize),
              (1 : usize),
              (12 : usize),
              (0 : usize),
              (2 : usize),
              (11 : usize),
              (7 : usize),
              (5 : usize),
              (3 : usize)],
         #v[(11 : usize),
              (8 : usize),
              (12 : usize),
              (0 : usize),
              (5 : usize),
              (2 : usize),
              (15 : usize),
              (13 : usize),
              (10 : usize),
              (14 : usize),
              (3 : usize),
              (6 : usize),
              (7 : usize),
              (1 : usize),
              (9 : usize),
              (4 : usize)],
         #v[(7 : usize),
              (9 : usize),
              (3 : usize),
              (1 : usize),
              (13 : usize),
              (12 : usize),
              (11 : usize),
              (14 : usize),
              (2 : usize),
              (6 : usize),
              (5 : usize),
              (10 : usize),
              (4 : usize),
              (0 : usize),
              (15 : usize),
              (8 : usize)],
         #v[(9 : usize),
              (0 : usize),
              (5 : usize),
              (7 : usize),
              (2 : usize),
              (4 : usize),
              (10 : usize),
              (15 : usize),
              (14 : usize),
              (1 : usize),
              (11 : usize),
              (12 : usize),
              (6 : usize),
              (8 : usize),
              (3 : usize),
              (13 : usize)],
         #v[(2 : usize),
              (12 : usize),
              (6 : usize),
              (10 : usize),
              (0 : usize),
              (11 : usize),
              (8 : usize),
              (3 : usize),
              (4 : usize),
              (13 : usize),
              (7 : usize),
              (5 : usize),
              (15 : usize),
              (14 : usize),
              (1 : usize),
              (9 : usize)],
         #v[(12 : usize),
              (5 : usize),
              (1 : usize),
              (15 : usize),
              (14 : usize),
              (13 : usize),
              (4 : usize),
              (10 : usize),
              (0 : usize),
              (7 : usize),
              (6 : usize),
              (3 : usize),
              (9 : usize),
              (2 : usize),
              (8 : usize),
              (11 : usize)],
         #v[(13 : usize),
              (11 : usize),
              (7 : usize),
              (14 : usize),
              (12 : usize),
              (1 : usize),
              (3 : usize),
              (9 : usize),
              (5 : usize),
              (0 : usize),
              (15 : usize),
              (4 : usize),
              (8 : usize),
              (6 : usize),
              (2 : usize),
              (10 : usize)],
         #v[(6 : usize),
              (15 : usize),
              (14 : usize),
              (9 : usize),
              (11 : usize),
              (3 : usize),
              (0 : usize),
              (8 : usize),
              (12 : usize),
              (2 : usize),
              (13 : usize),
              (7 : usize),
              (1 : usize),
              (4 : usize),
              (10 : usize),
              (5 : usize)],
         #v[(10 : usize),
              (2 : usize),
              (8 : usize),
              (4 : usize),
              (7 : usize),
              (6 : usize),
              (1 : usize),
              (5 : usize),
              (15 : usize),
              (11 : usize),
              (9 : usize),
              (14 : usize),
              (3 : usize),
              (12 : usize),
              (13 : usize),
              (0 : usize)]])
    (by rfl)

--  BLAKE2b initialization vector: fractional parts of sqrt(2..19) truncated to 64 bits.
def IV_B : (RustArray u64 8) :=
  RustM.of_isOk
    (do
    #v[(7640891576956012808 : u64),
         (13503953896175478587 : u64),
         (4354685564936845355 : u64),
         (11912009170470909681 : u64),
         (5840696475078001361 : u64),
         (11170449401992604703 : u64),
         (2270897969802886507 : u64),
         (6620516959819538809 : u64)])
    (by rfl)

--  BLAKE2b block size in bytes.
def BLOCK_B : usize := (128 : usize)

--  BLAKE2b mixing function G.
-- 
--  Operates on the 4x4 working state `v`, mixing in message words `x` and `y`
--  at positions `a`, `b`, `c`, `d`. Rotation amounts: 32, 24, 16, 63.
def g_b
    (v : (RustArray u64 16))
    (a : usize)
    (b : usize)
    (c : usize)
    (d : usize)
    (x : u64)
    (y : u64) :
    RustM (RustArray u64 16) := do
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      a
      (← (Core_models.Num.Impl_9.wrapping_add
        (← (Core_models.Num.Impl_9.wrapping_add (← v[a]_?) (← v[b]_?)))
        x)));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      d
      (← (Core_models.Num.Impl_9.rotate_right
        (← ((← v[d]_?) ^^^? (← v[a]_?)))
        (32 : u32))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      c
      (← (Core_models.Num.Impl_9.wrapping_add (← v[c]_?) (← v[d]_?))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      b
      (← (Core_models.Num.Impl_9.rotate_right
        (← ((← v[b]_?) ^^^? (← v[c]_?)))
        (24 : u32))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      a
      (← (Core_models.Num.Impl_9.wrapping_add
        (← (Core_models.Num.Impl_9.wrapping_add (← v[a]_?) (← v[b]_?)))
        y)));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      d
      (← (Core_models.Num.Impl_9.rotate_right
        (← ((← v[d]_?) ^^^? (← v[a]_?)))
        (16 : u32))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      c
      (← (Core_models.Num.Impl_9.wrapping_add (← v[c]_?) (← v[d]_?))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      b
      (← (Core_models.Num.Impl_9.rotate_right
        (← ((← v[b]_?) ^^^? (← v[c]_?)))
        (63 : u32))));
  (pure v)

--  BLAKE2b compression function.
-- 
--  Compresses one 128-byte block of message words `m` into the chaining value `h`.
--  `t` is the byte offset counter (up to 2^128), `last` signals the final block.
def compress_b
    (h : (RustArray u64 8))
    (m : (RustArray u64 16))
    (t : u128)
    (last : Bool) :
    RustM (RustArray u64 8) := do
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.repeat (0 : u64) (16 : usize));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun v _ => (do (pure true) : RustM Bool))
      v
      (fun v i =>
        (do
        let v : (RustArray u64 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            v
            i
            (← h[i]_?));
        let v : (RustArray u64 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            v
            (← (i +? (8 : usize)))
            (← IV_B[i]_?));
        (pure v) :
        RustM (RustArray u64 16))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      (12 : usize)
      (← ((← v[(12 : usize)]_?) ^^^? (← (Rust_primitives.Hax.cast_op t)))));
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      (13 : usize)
      (← ((← v[(13 : usize)]_?)
        ^^^? (← (Rust_primitives.Hax.cast_op (← (t >>>? (64 : i32))))))));
  let v : (RustArray u64 16) ←
    if last then
      let v : (RustArray u64 16) ←
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          v
          (14 : usize)
          (← (Rust_primitives.Hax.Machine_int.not (← v[(14 : usize)]_?))));
      (pure v)
    else
      (pure v);
  let v : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (12 : usize)
      (fun v _ => (do (pure true) : RustM Bool))
      v
      (fun v i =>
        (do
        let s : (RustArray usize 16) ← SIGMA[(← (i %? (10 : usize)))]_?;
        let v : (RustArray u64 16) ←
          (g_b
            v
            (0 : usize)
            (4 : usize)
            (8 : usize)
            (12 : usize)
            (← m[(← s[(0 : usize)]_?)]_?)
            (← m[(← s[(1 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (1 : usize)
            (5 : usize)
            (9 : usize)
            (13 : usize)
            (← m[(← s[(2 : usize)]_?)]_?)
            (← m[(← s[(3 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (2 : usize)
            (6 : usize)
            (10 : usize)
            (14 : usize)
            (← m[(← s[(4 : usize)]_?)]_?)
            (← m[(← s[(5 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (3 : usize)
            (7 : usize)
            (11 : usize)
            (15 : usize)
            (← m[(← s[(6 : usize)]_?)]_?)
            (← m[(← s[(7 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (0 : usize)
            (5 : usize)
            (10 : usize)
            (15 : usize)
            (← m[(← s[(8 : usize)]_?)]_?)
            (← m[(← s[(9 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (1 : usize)
            (6 : usize)
            (11 : usize)
            (12 : usize)
            (← m[(← s[(10 : usize)]_?)]_?)
            (← m[(← s[(11 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (2 : usize)
            (7 : usize)
            (8 : usize)
            (13 : usize)
            (← m[(← s[(12 : usize)]_?)]_?)
            (← m[(← s[(13 : usize)]_?)]_?));
        let v : (RustArray u64 16) ←
          (g_b
            v
            (3 : usize)
            (4 : usize)
            (9 : usize)
            (14 : usize)
            (← m[(← s[(14 : usize)]_?)]_?)
            (← m[(← s[(15 : usize)]_?)]_?));
        (pure v) :
        RustM (RustArray u64 16))));
  let result : (RustArray u64 8) ←
    (Rust_primitives.Hax.repeat (0 : u64) (8 : usize));
  let result : (RustArray u64 8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          i
          (← ((← ((← h[i]_?) ^^^? (← v[i]_?)))
            ^^^? (← v[(← (i +? (8 : usize)))]_?)))) :
        RustM (RustArray u64 8))));
  (pure result)

--  Decode a slice of bytes into an array of `u64` words (little-endian).
def bytes_to_words_b (block : (RustSlice u8)) : RustM (RustArray u64 16) := do
  let m : (RustArray u64 16) ←
    (Rust_primitives.Hax.repeat (0 : u64) (16 : usize));
  let m : (RustArray u64 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun m _ => (do (pure true) : RustM Bool))
      m
      (fun m i =>
        (do
        let base : usize ← (i *? (8 : usize));
        if
        (← (Rust_primitives.Hax.Machine_int.le
          (← (base +? (8 : usize)))
          (← (Core_models.Slice.Impl.len u8 block)))) then
          let m : (RustArray u64 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              m
              i
              (← (Core_models.Num.Impl_9.from_le_bytes
                #v[(← block[base]_?),
                     (← block[(← (base +? (1 : usize)))]_?),
                     (← block[(← (base +? (2 : usize)))]_?),
                     (← block[(← (base +? (3 : usize)))]_?),
                     (← block[(← (base +? (4 : usize)))]_?),
                     (← block[(← (base +? (5 : usize)))]_?),
                     (← block[(← (base +? (6 : usize)))]_?),
                     (← block[(← (base +? (7 : usize)))]_?)])));
          (pure m)
        else
          let buf : (RustArray u8 8) ←
            (Rust_primitives.Hax.repeat (0 : u8) (8 : usize));
          let buf : (RustArray u8 8) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (8 : usize)
              (fun buf _ => (do (pure true) : RustM Bool))
              buf
              (fun buf j =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← (base +? j))
                  (← (Core_models.Slice.Impl.len u8 block)))) then
                  let buf : (RustArray u8 8) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      buf
                      j
                      (← block[(← (base +? j))]_?));
                  (pure buf)
                else
                  (pure buf) :
                RustM (RustArray u8 8))));
          let m : (RustArray u64 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              m
              i
              (← (Core_models.Num.Impl_9.from_le_bytes buf)));
          (pure m) :
        RustM (RustArray u64 16))));
  (pure m)

--  BLAKE2b hash function (RFC 7693).
-- 
--  - `msg`: input message (arbitrary length).
--  - `key`: optional key (0 to 64 bytes). Pass `&[]` for unkeyed hashing.
--  - `out_len`: desired output length in bytes (1 to 64).
-- 
--  Returns the hash as a `Vec<u8>` of length `out_len`.
-- 
--  # Panics
-- 
--  Panics if `out_len` is not in 1..=64 or `key.len()` exceeds 64.
def blake2b (msg : (RustSlice u8)) (key : (RustSlice u8)) (out_len : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let _ ←
    if
    (← (Core_models.Ops.Bit.Not.not
      (← ((← (Rust_primitives.Hax.Machine_int.ge out_len (1 : usize)))
        &&? (← (Rust_primitives.Hax.Machine_int.le out_len (64 : usize)))))))
    then
      (Rust_primitives.Hax.never_to_any
        (← (Core_models.Panicking.panic_fmt
          (← (Core_models.Fmt.Rt.Impl_1.new_const ((1 : usize))
            #v["blake2b: out_len must be 1..64"])))))
    else
      (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ←
    if
    (← (Core_models.Ops.Bit.Not.not
      (← (Rust_primitives.Hax.Machine_int.le
        (← (Core_models.Slice.Impl.len u8 key))
        (64 : usize))))) then
      (Rust_primitives.Hax.never_to_any
        (← (Core_models.Panicking.panic_fmt
          (← (Core_models.Fmt.Rt.Impl_1.new_const ((1 : usize))
            #v["blake2b: key length must be 0..64"])))))
    else
      (pure Rust_primitives.Hax.Tuple0.mk);
  let key_len : usize ← (Core_models.Slice.Impl.len u8 key);
  let h : (RustArray u64 8) := IV_B;
  let h : (RustArray u64 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      h
      (0 : usize)
      (← ((← h[(0 : usize)]_?)
        ^^^? (← ((← ((16842752 : u64)
            ^^^? (← ((← (Rust_primitives.Hax.cast_op key_len))
              <<<? (8 : i32)))))
          ^^^? (← (Rust_primitives.Hax.cast_op out_len)))))));
  let data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    if (← (Rust_primitives.Hax.Machine_int.gt key_len (0 : usize))) then
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl.with_capacity u8
          (← (BLOCK_B +? (← (Core_models.Slice.Impl.len u8 msg)))));
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global d key);
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.resize u8 Alloc.Alloc.Global d BLOCK_B (0 : u8));
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global d msg);
      (pure d)
    else
      (Alloc.Slice.Impl.to_vec u8 msg);
  let h : (RustArray u64 8) ←
    if (← (Alloc.Vec.Impl_1.is_empty u8 Alloc.Alloc.Global data)) then
      let block : (RustArray u8 128) ←
        (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
      let m : (RustArray u64 16) ←
        (bytes_to_words_b (← (Rust_primitives.unsize block)));
      let h : (RustArray u64 8) ← (compress_b h m (0 : u128) true);
      (pure h)
    else
      let total : usize ← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global data);
      let offset : usize := (0 : usize);
      let ⟨h, offset⟩ ←
        (Rust_primitives.Hax.while_loop
          (fun ⟨h, offset⟩ => (do (pure true) : RustM Bool))
          (fun ⟨h, offset⟩ =>
            (do (Rust_primitives.Hax.Machine_int.lt offset total) : RustM Bool))
          (fun ⟨h, offset⟩ =>
            (do
            (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
            RustM Hax_lib.Int.Int))
          (Rust_primitives.Hax.Tuple2.mk h offset)
          (fun ⟨h, offset⟩ =>
            (do
            let remaining : usize ← (total -? offset);
            let take : usize ←
              if (← (Rust_primitives.Hax.Machine_int.gt remaining BLOCK_B)) then
                (pure BLOCK_B)
              else
                (pure remaining);
            let last : Bool ←
              (Rust_primitives.Hax.Machine_int.le remaining BLOCK_B);
            let block : (RustArray u8 128) ←
              (Rust_primitives.Hax.repeat (0 : u8) (128 : usize));
            let block : (RustArray u8 128) ←
              (Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                take
                (fun block _ => (do (pure true) : RustM Bool))
                block
                (fun block i =>
                  (do
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    block
                    i
                    (← data[(← (offset +? i))]_?)) :
                  RustM (RustArray u8 128))));
            let bytes_compressed : usize ← (offset +? take);
            let t : u128 ← (Rust_primitives.Hax.cast_op bytes_compressed);
            let m : (RustArray u64 16) ←
              (bytes_to_words_b (← (Rust_primitives.unsize block)));
            let h : (RustArray u64 8) ← (compress_b h m t last);
            let offset : usize ← (offset +? take);
            (pure (Rust_primitives.Hax.Tuple2.mk h offset)) :
            RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 8) usize))));
      (pure h);
  let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8 out_len);
  let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let word_bytes : (RustArray u8 8) ←
          (Core_models.Num.Impl_9.to_le_bytes (← h[i]_?));
        (Core_models.Iter.Traits.Iterator.Iterator.fold
          (← (Core_models.Iter.Traits.Collect.IntoIterator.into_iter
            (RustArray u8 8) word_bytes))
          out
          (fun out b =>
            (do
            if
            (← (Rust_primitives.Hax.Machine_int.lt
              (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global out))
              out_len)) then
              let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global out b);
              (pure out)
            else
              (pure out) :
            RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  (pure out)

--  BLAKE2s initialization vector: fractional parts of sqrt(2..19) truncated to 32 bits.
def IV_S : (RustArray u32 8) :=
  RustM.of_isOk
    (do
    #v[(1779033703 : u32),
         (3144134277 : u32),
         (1013904242 : u32),
         (2773480762 : u32),
         (1359893119 : u32),
         (2600822924 : u32),
         (528734635 : u32),
         (1541459225 : u32)])
    (by rfl)

--  BLAKE2s block size in bytes.
def BLOCK_S : usize := (64 : usize)

--  BLAKE2s mixing function G.
-- 
--  Operates on the 4x4 working state `v`, mixing in message words `x` and `y`
--  at positions `a`, `b`, `c`, `d`. Rotation amounts: 16, 12, 8, 7.
def g_s
    (v : (RustArray u32 16))
    (a : usize)
    (b : usize)
    (c : usize)
    (d : usize)
    (x : u32)
    (y : u32) :
    RustM (RustArray u32 16) := do
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      a
      (← (Core_models.Num.Impl_8.wrapping_add
        (← (Core_models.Num.Impl_8.wrapping_add (← v[a]_?) (← v[b]_?)))
        x)));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      d
      (← (Core_models.Num.Impl_8.rotate_right
        (← ((← v[d]_?) ^^^? (← v[a]_?)))
        (16 : u32))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      c
      (← (Core_models.Num.Impl_8.wrapping_add (← v[c]_?) (← v[d]_?))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      b
      (← (Core_models.Num.Impl_8.rotate_right
        (← ((← v[b]_?) ^^^? (← v[c]_?)))
        (12 : u32))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      a
      (← (Core_models.Num.Impl_8.wrapping_add
        (← (Core_models.Num.Impl_8.wrapping_add (← v[a]_?) (← v[b]_?)))
        y)));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      d
      (← (Core_models.Num.Impl_8.rotate_right
        (← ((← v[d]_?) ^^^? (← v[a]_?)))
        (8 : u32))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      c
      (← (Core_models.Num.Impl_8.wrapping_add (← v[c]_?) (← v[d]_?))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      b
      (← (Core_models.Num.Impl_8.rotate_right
        (← ((← v[b]_?) ^^^? (← v[c]_?)))
        (7 : u32))));
  (pure v)

--  BLAKE2s compression function.
-- 
--  Compresses one 64-byte block of message words `m` into the chaining value `h`.
--  `t` is the byte offset counter (up to 2^64), `last` signals the final block.
def compress_s
    (h : (RustArray u32 8))
    (m : (RustArray u32 16))
    (t : u64)
    (last : Bool) :
    RustM (RustArray u32 8) := do
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.repeat (0 : u32) (16 : usize));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun v _ => (do (pure true) : RustM Bool))
      v
      (fun v i =>
        (do
        let v : (RustArray u32 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            v
            i
            (← h[i]_?));
        let v : (RustArray u32 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            v
            (← (i +? (8 : usize)))
            (← IV_S[i]_?));
        (pure v) :
        RustM (RustArray u32 16))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      (12 : usize)
      (← ((← v[(12 : usize)]_?) ^^^? (← (Rust_primitives.Hax.cast_op t)))));
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      v
      (13 : usize)
      (← ((← v[(13 : usize)]_?)
        ^^^? (← (Rust_primitives.Hax.cast_op (← (t >>>? (32 : i32))))))));
  let v : (RustArray u32 16) ←
    if last then
      let v : (RustArray u32 16) ←
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          v
          (14 : usize)
          (← (Rust_primitives.Hax.Machine_int.not (← v[(14 : usize)]_?))));
      (pure v)
    else
      (pure v);
  let v : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (10 : usize)
      (fun v _ => (do (pure true) : RustM Bool))
      v
      (fun v i =>
        (do
        let s : (RustArray usize 16) ← SIGMA[i]_?;
        let v : (RustArray u32 16) ←
          (g_s
            v
            (0 : usize)
            (4 : usize)
            (8 : usize)
            (12 : usize)
            (← m[(← s[(0 : usize)]_?)]_?)
            (← m[(← s[(1 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (1 : usize)
            (5 : usize)
            (9 : usize)
            (13 : usize)
            (← m[(← s[(2 : usize)]_?)]_?)
            (← m[(← s[(3 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (2 : usize)
            (6 : usize)
            (10 : usize)
            (14 : usize)
            (← m[(← s[(4 : usize)]_?)]_?)
            (← m[(← s[(5 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (3 : usize)
            (7 : usize)
            (11 : usize)
            (15 : usize)
            (← m[(← s[(6 : usize)]_?)]_?)
            (← m[(← s[(7 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (0 : usize)
            (5 : usize)
            (10 : usize)
            (15 : usize)
            (← m[(← s[(8 : usize)]_?)]_?)
            (← m[(← s[(9 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (1 : usize)
            (6 : usize)
            (11 : usize)
            (12 : usize)
            (← m[(← s[(10 : usize)]_?)]_?)
            (← m[(← s[(11 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (2 : usize)
            (7 : usize)
            (8 : usize)
            (13 : usize)
            (← m[(← s[(12 : usize)]_?)]_?)
            (← m[(← s[(13 : usize)]_?)]_?));
        let v : (RustArray u32 16) ←
          (g_s
            v
            (3 : usize)
            (4 : usize)
            (9 : usize)
            (14 : usize)
            (← m[(← s[(14 : usize)]_?)]_?)
            (← m[(← s[(15 : usize)]_?)]_?));
        (pure v) :
        RustM (RustArray u32 16))));
  let result : (RustArray u32 8) ←
    (Rust_primitives.Hax.repeat (0 : u32) (8 : usize));
  let result : (RustArray u32 8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          result
          i
          (← ((← ((← h[i]_?) ^^^? (← v[i]_?)))
            ^^^? (← v[(← (i +? (8 : usize)))]_?)))) :
        RustM (RustArray u32 8))));
  (pure result)

--  Decode a slice of bytes into an array of `u32` words (little-endian).
def bytes_to_words_s (block : (RustSlice u8)) : RustM (RustArray u32 16) := do
  let m : (RustArray u32 16) ←
    (Rust_primitives.Hax.repeat (0 : u32) (16 : usize));
  let m : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun m _ => (do (pure true) : RustM Bool))
      m
      (fun m i =>
        (do
        let base : usize ← (i *? (4 : usize));
        if
        (← (Rust_primitives.Hax.Machine_int.le
          (← (base +? (4 : usize)))
          (← (Core_models.Slice.Impl.len u8 block)))) then
          let m : (RustArray u32 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              m
              i
              (← (Core_models.Num.Impl_8.from_le_bytes
                #v[(← block[base]_?),
                     (← block[(← (base +? (1 : usize)))]_?),
                     (← block[(← (base +? (2 : usize)))]_?),
                     (← block[(← (base +? (3 : usize)))]_?)])));
          (pure m)
        else
          let buf : (RustArray u8 4) ←
            (Rust_primitives.Hax.repeat (0 : u8) (4 : usize));
          let buf : (RustArray u8 4) ←
            (Rust_primitives.Hax.Folds.fold_range
              (0 : usize)
              (4 : usize)
              (fun buf _ => (do (pure true) : RustM Bool))
              buf
              (fun buf j =>
                (do
                if
                (← (Rust_primitives.Hax.Machine_int.lt
                  (← (base +? j))
                  (← (Core_models.Slice.Impl.len u8 block)))) then
                  let buf : (RustArray u8 4) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      buf
                      j
                      (← block[(← (base +? j))]_?));
                  (pure buf)
                else
                  (pure buf) :
                RustM (RustArray u8 4))));
          let m : (RustArray u32 16) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              m
              i
              (← (Core_models.Num.Impl_8.from_le_bytes buf)));
          (pure m) :
        RustM (RustArray u32 16))));
  (pure m)

--  BLAKE2s hash function (RFC 7693).
-- 
--  - `msg`: input message (arbitrary length).
--  - `key`: optional key (0 to 32 bytes). Pass `&[]` for unkeyed hashing.
--  - `out_len`: desired output length in bytes (1 to 32).
-- 
--  Returns the hash as a `Vec<u8>` of length `out_len`.
-- 
--  # Panics
-- 
--  Panics if `out_len` is not in 1..=32 or `key.len()` exceeds 32.
def blake2s (msg : (RustSlice u8)) (key : (RustSlice u8)) (out_len : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let _ ←
    if
    (← (Core_models.Ops.Bit.Not.not
      (← ((← (Rust_primitives.Hax.Machine_int.ge out_len (1 : usize)))
        &&? (← (Rust_primitives.Hax.Machine_int.le out_len (32 : usize)))))))
    then
      (Rust_primitives.Hax.never_to_any
        (← (Core_models.Panicking.panic_fmt
          (← (Core_models.Fmt.Rt.Impl_1.new_const ((1 : usize))
            #v["blake2s: out_len must be 1..32"])))))
    else
      (pure Rust_primitives.Hax.Tuple0.mk);
  let _ ←
    if
    (← (Core_models.Ops.Bit.Not.not
      (← (Rust_primitives.Hax.Machine_int.le
        (← (Core_models.Slice.Impl.len u8 key))
        (32 : usize))))) then
      (Rust_primitives.Hax.never_to_any
        (← (Core_models.Panicking.panic_fmt
          (← (Core_models.Fmt.Rt.Impl_1.new_const ((1 : usize))
            #v["blake2s: key length must be 0..32"])))))
    else
      (pure Rust_primitives.Hax.Tuple0.mk);
  let key_len : usize ← (Core_models.Slice.Impl.len u8 key);
  let h : (RustArray u32 8) := IV_S;
  let h : (RustArray u32 8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      h
      (0 : usize)
      (← ((← h[(0 : usize)]_?)
        ^^^? (← ((← ((16842752 : u32)
            ^^^? (← ((← (Rust_primitives.Hax.cast_op key_len))
              <<<? (8 : i32)))))
          ^^^? (← (Rust_primitives.Hax.cast_op out_len)))))));
  let data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    if (← (Rust_primitives.Hax.Machine_int.gt key_len (0 : usize))) then
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl.with_capacity u8
          (← (BLOCK_S +? (← (Core_models.Slice.Impl.len u8 msg)))));
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global d key);
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.resize u8 Alloc.Alloc.Global d BLOCK_S (0 : u8));
      let d : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
        (Alloc.Vec.Impl_2.extend_from_slice u8 Alloc.Alloc.Global d msg);
      (pure d)
    else
      (Alloc.Slice.Impl.to_vec u8 msg);
  let h : (RustArray u32 8) ←
    if (← (Alloc.Vec.Impl_1.is_empty u8 Alloc.Alloc.Global data)) then
      let block : (RustArray u8 64) ←
        (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
      let m : (RustArray u32 16) ←
        (bytes_to_words_s (← (Rust_primitives.unsize block)));
      let h : (RustArray u32 8) ← (compress_s h m (0 : u64) true);
      (pure h)
    else
      let total : usize ← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global data);
      let offset : usize := (0 : usize);
      let ⟨h, offset⟩ ←
        (Rust_primitives.Hax.while_loop
          (fun ⟨h, offset⟩ => (do (pure true) : RustM Bool))
          (fun ⟨h, offset⟩ =>
            (do (Rust_primitives.Hax.Machine_int.lt offset total) : RustM Bool))
          (fun ⟨h, offset⟩ =>
            (do
            (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
            RustM Hax_lib.Int.Int))
          (Rust_primitives.Hax.Tuple2.mk h offset)
          (fun ⟨h, offset⟩ =>
            (do
            let remaining : usize ← (total -? offset);
            let take : usize ←
              if (← (Rust_primitives.Hax.Machine_int.gt remaining BLOCK_S)) then
                (pure BLOCK_S)
              else
                (pure remaining);
            let last : Bool ←
              (Rust_primitives.Hax.Machine_int.le remaining BLOCK_S);
            let block : (RustArray u8 64) ←
              (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
            let block : (RustArray u8 64) ←
              (Rust_primitives.Hax.Folds.fold_range
                (0 : usize)
                take
                (fun block _ => (do (pure true) : RustM Bool))
                block
                (fun block i =>
                  (do
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    block
                    i
                    (← data[(← (offset +? i))]_?)) :
                  RustM (RustArray u8 64))));
            let bytes_compressed : usize ← (offset +? take);
            let t : u64 ← (Rust_primitives.Hax.cast_op bytes_compressed);
            let m : (RustArray u32 16) ←
              (bytes_to_words_s (← (Rust_primitives.unsize block)));
            let h : (RustArray u32 8) ← (compress_s h m t last);
            let offset : usize ← (offset +? take);
            (pure (Rust_primitives.Hax.Tuple2.mk h offset)) :
            RustM (Rust_primitives.Hax.Tuple2 (RustArray u32 8) usize))));
      (pure h);
  let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8 out_len);
  let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        let word_bytes : (RustArray u8 4) ←
          (Core_models.Num.Impl_8.to_le_bytes (← h[i]_?));
        (Core_models.Iter.Traits.Iterator.Iterator.fold
          (← (Core_models.Iter.Traits.Collect.IntoIterator.into_iter
            (RustArray u8 4) word_bytes))
          out
          (fun out b =>
            (do
            if
            (← (Rust_primitives.Hax.Machine_int.lt
              (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global out))
              out_len)) then
              let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global out b);
              (pure out)
            else
              (pure out) :
            RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  (pure out)

end Libcrux_specs_hax.Blake2


namespace Libcrux_specs_hax.Hmac

--  HMAC block size for SHA-256 (512 bits = 64 bytes).
def BLOCK_SIZE : usize := (64 : usize)

--  Inner padding byte (RFC 2104, Section 2).
def IPAD : u8 := (54 : u8)

--  Outer padding byte (RFC 2104, Section 2).
def OPAD : u8 := (92 : u8)

--  Compute HMAC-SHA256 of `msg` under `key`.
-- 
--  1. If `key` is longer than 64 bytes, replace it with SHA-256(key).
--  2. Pad the (possibly hashed) key to 64 bytes with zeros.
--  3. inner = SHA-256((key_padded XOR ipad) || msg)
--  4. result = SHA-256((key_padded XOR opad) || inner)
def hmac_sha256 (key : (RustSlice u8)) (msg : (RustSlice u8)) :
    RustM (RustArray u8 32) := do
  let key_hash : (RustArray u8 32) ←
    if
    (← (Rust_primitives.Hax.Machine_int.gt
      (← (Core_models.Slice.Impl.len u8 key))
      BLOCK_SIZE)) then
      (Libcrux_specs_hax.Sha256.sha256 key)
    else
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let key_bytes : (RustSlice u8) ←
    if
    (← (Rust_primitives.Hax.Machine_int.gt
      (← (Core_models.Slice.Impl.len u8 key))
      BLOCK_SIZE)) then
      (Rust_primitives.unsize key_hash)
    else
      (pure key);
  let key_padded : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let key_padded : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core_models.Slice.Impl.len u8 key_bytes))
      (fun key_padded _ => (do (pure true) : RustM Bool))
      key_padded
      (fun key_padded i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          key_padded
          i
          (← key_bytes[i]_?)) :
        RustM (RustArray u8 64))));
  let inner_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let inner_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      BLOCK_SIZE
      (fun inner_key _ => (do (pure true) : RustM Bool))
      inner_key
      (fun inner_key i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          inner_key
          i
          (← ((← key_padded[i]_?) ^^^? IPAD))) :
        RustM (RustArray u8 64))));
  let inner_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8
      (← (BLOCK_SIZE +? (← (Core_models.Slice.Impl.len u8 msg)))));
  let inner_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      BLOCK_SIZE
      (fun inner_data _ => (do (pure true) : RustM Bool))
      inner_data
      (fun inner_data i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
          inner_data
          (← inner_key[i]_?)) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let inner_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core_models.Slice.Impl.len u8 msg))
      (fun inner_data _ => (do (pure true) : RustM Bool))
      inner_data
      (fun inner_data i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global inner_data (← msg[i]_?)) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let inner_hash : (RustArray u8 32) ←
    (Libcrux_specs_hax.Sha256.sha256
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) inner_data)));
  let outer_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let outer_key : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      BLOCK_SIZE
      (fun outer_key _ => (do (pure true) : RustM Bool))
      outer_key
      (fun outer_key i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          outer_key
          i
          (← ((← key_padded[i]_?) ^^^? OPAD))) :
        RustM (RustArray u8 64))));
  let outer_data : (RustArray u8 96) ←
    (Rust_primitives.Hax.repeat (0 : u8) (96 : usize));
  let outer_data : (RustArray u8 96) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      BLOCK_SIZE
      (fun outer_data _ => (do (pure true) : RustM Bool))
      outer_data
      (fun outer_data i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          outer_data
          i
          (← outer_key[i]_?)) :
        RustM (RustArray u8 96))));
  let outer_data : (RustArray u8 96) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (32 : usize)
      (fun outer_data _ => (do (pure true) : RustM Bool))
      outer_data
      (fun outer_data i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          outer_data
          (← (BLOCK_SIZE +? i))
          (← inner_hash[i]_?)) :
        RustM (RustArray u8 96))));
  (Libcrux_specs_hax.Sha256.sha256 (← (Rust_primitives.unsize outer_data)))

--  Fixed-length wrapper: HMAC-SHA256 on 32-byte key and message.
def hmac_sha256_32 (key : (RustArray u8 32)) (msg : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  (hmac_sha256
    (← (Rust_primitives.unsize key))
    (← (Rust_primitives.unsize msg)))

end Libcrux_specs_hax.Hmac


namespace Libcrux_specs_hax.Hkdf

--  SHA-256 output length in bytes.
def HASH_LEN : usize := (32 : usize)

--  HKDF-Extract: PRK = HMAC-SHA256(salt, IKM).
-- 
--  If `salt` is empty, a string of `HASH_LEN` zeros is used as the salt
--  (per RFC 5869, Section 2.2).
def hkdf_extract (salt : (RustSlice u8)) (ikm : (RustSlice u8)) :
    RustM (RustArray u8 32) := do
  let default_salt : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let actual_salt : (RustSlice u8) ←
    if (← (Core_models.Slice.Impl.is_empty u8 salt)) then
      default_salt[Core_models.Ops.Range.RangeFull.mk]_?
    else
      (pure salt);
  (Libcrux_specs_hax.Hmac.hmac_sha256 actual_salt ikm)

--  HKDF-Expand: derive `length` bytes of output keying material from PRK and info.
-- 
--  T(0) = empty string
--  T(i) = HMAC-SHA256(PRK, T(i-1) || info || i)   for i = 1, 2, ...
--  OKM  = first `length` bytes of T(1) || T(2) || ...
-- 
--  Panics if `length` > 255 * HASH_LEN (per RFC 5869, Section 2.3).
def hkdf_expand
    (prk : (RustArray u8 32))
    (info : (RustSlice u8))
    (length : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let n : usize ← ((← ((← (length +? HASH_LEN)) -? (1 : usize))) /? HASH_LEN);
  let _ ←
    if
    (← (Core_models.Ops.Bit.Not.not
      (← (Rust_primitives.Hax.Machine_int.le n (255 : usize))))) then
      (Rust_primitives.Hax.never_to_any
        (← (Core_models.Panicking.panic_fmt
          (← (Core_models.Fmt.Rt.Impl_1.new_const ((1 : usize))
            #v["HKDF-Expand: length too large (max 255 * 32 = 8160 bytes)"])))))
    else
      (pure Rust_primitives.Hax.Tuple0.mk);
  let okm : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8 (← (n *? HASH_LEN)));
  let t_prev : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let ⟨okm, t_prev⟩ ←
    (Core_models.Iter.Traits.Iterator.Iterator.fold
      (← (Core_models.Iter.Traits.Collect.IntoIterator.into_iter
        (Core_models.Ops.Range.RangeInclusive usize)
        (← (Core_models.Ops.Range.Impl_7.new usize (1 : usize) n))))
      (Rust_primitives.Hax.Tuple2.mk okm t_prev)
      (fun ⟨okm, t_prev⟩ i =>
        (do
        let hmac_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl.with_capacity u8
            (← ((← ((← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global t_prev))
                +? (← (Core_models.Slice.Impl.len u8 info))))
              +? (1 : usize))));
        let hmac_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global t_prev))
            (fun hmac_input _ => (do (pure true) : RustM Bool))
            hmac_input
            (fun hmac_input j =>
              (do
              (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                hmac_input
                (← t_prev[j]_?)) :
              RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
        let hmac_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (← (Core_models.Slice.Impl.len u8 info))
            (fun hmac_input _ => (do (pure true) : RustM Bool))
            hmac_input
            (fun hmac_input j =>
              (do
              (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                hmac_input
                (← info[j]_?)) :
              RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
        let hmac_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            hmac_input
            (← (Rust_primitives.Hax.cast_op i)));
        let t_i : (RustArray u8 32) ←
          (Libcrux_specs_hax.Hmac.hmac_sha256
            (← (Rust_primitives.unsize prk))
            (← (Core_models.Ops.Deref.Deref.deref
              (Alloc.Vec.Vec u8 Alloc.Alloc.Global) hmac_input)));
        let okm : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            HASH_LEN
            (fun okm _ => (do (pure true) : RustM Bool))
            okm
            (fun okm j =>
              (do
              (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global okm (← t_i[j]_?)) :
              RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
        let t_prev : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl.with_capacity u8 HASH_LEN);
        let t_prev : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            HASH_LEN
            (fun t_prev _ => (do (pure true) : RustM Bool))
            t_prev
            (fun t_prev j =>
              (do
              (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global t_prev (← t_i[j]_?))
              :
              RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
        (pure (Rust_primitives.Hax.Tuple2.mk okm t_prev)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let okm : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl_1.truncate u8 Alloc.Alloc.Global okm length);
  (pure okm)

--  Full HKDF: extract then expand.
-- 
--  Equivalent to `hkdf_expand(&hkdf_extract(salt, ikm), info, length)`.
def hkdf
    (salt : (RustSlice u8))
    (ikm : (RustSlice u8))
    (info : (RustSlice u8))
    (length : usize) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let prk : (RustArray u8 32) ← (hkdf_extract salt ikm);
  (hkdf_expand prk info length)

--  Fixed-length wrapper: HKDF-Extract with 32-byte salt and IKM.
def hkdf_extract_32 (salt : (RustArray u8 32)) (ikm : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  (hkdf_extract
    (← (Rust_primitives.unsize salt))
    (← (Rust_primitives.unsize ikm)))

--  Fixed-length wrapper: HKDF-Expand with 32-byte PRK and info, 32-byte output.
def hkdf_expand_32 (prk : (RustArray u8 32)) (info : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  let out : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (hkdf_expand prk (← (Rust_primitives.unsize info)) (32 : usize));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let result : (RustArray u8 32) ←
    (Core_models.Slice.Impl.copy_from_slice u8
      result
      (← out[(Core_models.Ops.Range.RangeTo.mk (_end := (32 : usize)))]_?));
  (pure result)

end Libcrux_specs_hax.Hkdf


namespace Libcrux_specs_hax.Chacha20

--  ChaCha20 constants: "expand 32-byte k" as four little-endian u32 words.
def CONSTANTS : (RustArray u32 4) :=
  RustM.of_isOk
    (do
    #v[(1634760805 : u32),
         (857760878 : u32),
         (2036477234 : u32),
         (1797285236 : u32)])
    (by rfl)

--  Read a little-endian u32 from a byte slice at the given offset.
def u32_from_le_bytes (bytes : (RustSlice u8)) (offset : usize) :
    RustM u32 := do
  (Rust_primitives.Hax.Machine_int.bitor
    (← (Rust_primitives.Hax.Machine_int.bitor
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← (Rust_primitives.Hax.cast_op (← bytes[offset]_?)))
        (← ((← (Rust_primitives.Hax.cast_op
            (← bytes[(← (offset +? (1 : usize)))]_?)))
          <<<? (8 : i32)))))
      (← ((← (Rust_primitives.Hax.cast_op
          (← bytes[(← (offset +? (2 : usize)))]_?)))
        <<<? (16 : i32)))))
    (← ((← (Rust_primitives.Hax.cast_op
        (← bytes[(← (offset +? (3 : usize)))]_?)))
      <<<? (24 : i32))))

--  Write a u32 as little-endian bytes into an array at the given offset.
def u32_to_le_bytes (value : u32) (out : (RustSlice u8)) (offset : usize) :
    RustM (RustSlice u8) := do
  let out : (RustSlice u8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      offset
      (← (Rust_primitives.Hax.cast_op value)));
  let out : (RustSlice u8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (← (offset +? (1 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (value >>>? (8 : i32))))));
  let out : (RustSlice u8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (← (offset +? (2 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (value >>>? (16 : i32))))));
  let out : (RustSlice u8) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (← (offset +? (3 : usize)))
      (← (Rust_primitives.Hax.cast_op (← (value >>>? (24 : i32))))));
  (pure out)

--  ChaCha20 quarter round (RFC 8439, Section 2.1).
-- 
--  Operates in-place on four elements of the state matrix identified
--  by indices a, b, c, d.
def quarter_round
    (state : (RustArray u32 16))
    (a : usize)
    (b : usize)
    (c : usize)
    (d : usize) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      a
      (← (Core_models.Num.Impl_8.wrapping_add (← state[a]_?) (← state[b]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      d
      (← ((← state[d]_?) ^^^? (← state[a]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      d
      (← (Core_models.Num.Impl_8.rotate_left (← state[d]_?) (16 : u32))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      c
      (← (Core_models.Num.Impl_8.wrapping_add (← state[c]_?) (← state[d]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      b
      (← ((← state[b]_?) ^^^? (← state[c]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      b
      (← (Core_models.Num.Impl_8.rotate_left (← state[b]_?) (12 : u32))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      a
      (← (Core_models.Num.Impl_8.wrapping_add (← state[a]_?) (← state[b]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      d
      (← ((← state[d]_?) ^^^? (← state[a]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      d
      (← (Core_models.Num.Impl_8.rotate_left (← state[d]_?) (8 : u32))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      c
      (← (Core_models.Num.Impl_8.wrapping_add (← state[c]_?) (← state[d]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      b
      (← ((← state[b]_?) ^^^? (← state[c]_?))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      b
      (← (Core_models.Num.Impl_8.rotate_left (← state[b]_?) (7 : u32))));
  (pure state)

--  Perform the 20-round ChaCha20 inner block function (10 double rounds).
-- 
--  Each double round consists of four column quarter rounds followed by
--  four diagonal quarter rounds.
def chacha20_inner_block (state : (RustArray u32 16)) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : i32)
      (10 : i32)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state _ =>
        (do
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (0 : usize)
            (4 : usize)
            (8 : usize)
            (12 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (1 : usize)
            (5 : usize)
            (9 : usize)
            (13 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (2 : usize)
            (6 : usize)
            (10 : usize)
            (14 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (3 : usize)
            (7 : usize)
            (11 : usize)
            (15 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (0 : usize)
            (5 : usize)
            (10 : usize)
            (15 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (1 : usize)
            (6 : usize)
            (11 : usize)
            (12 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (2 : usize)
            (7 : usize)
            (8 : usize)
            (13 : usize));
        let state : (RustArray u32 16) ←
          (quarter_round
            state
            (3 : usize)
            (4 : usize)
            (9 : usize)
            (14 : usize));
        (pure state) :
        RustM (RustArray u32 16))));
  (pure state)

--  Initialize the ChaCha20 state from key, nonce, and block counter.
-- 
--  State layout (4x4 u32 matrix):
--  - Words 0..3:   constants ("expand 32-byte k")
--  - Words 4..11:  key (8 little-endian u32 words from 32 bytes)
--  - Word 12:      block counter
--  - Words 13..15: nonce (3 little-endian u32 words from 12 bytes)
def chacha20_init
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (counter : u32) :
    RustM (RustArray u32 16) := do
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.repeat (0 : u32) (16 : usize));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (0 : usize)
      (← CONSTANTS[(0 : usize)]_?));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (1 : usize)
      (← CONSTANTS[(1 : usize)]_?));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (2 : usize)
      (← CONSTANTS[(2 : usize)]_?));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (3 : usize)
      (← CONSTANTS[(3 : usize)]_?));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          (← ((4 : usize) +? i))
          (← (u32_from_le_bytes
            (← (Rust_primitives.unsize key))
            (← ((4 : usize) *? i))))) :
        RustM (RustArray u32 16))));
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      state
      (12 : usize)
      counter);
  let state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (3 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          state
          (← ((13 : usize) +? i))
          (← (u32_from_le_bytes
            (← (Rust_primitives.unsize nonce))
            (← ((4 : usize) *? i))))) :
        RustM (RustArray u32 16))));
  (pure state)

--  Generate one 64-byte keystream block (RFC 8439, Section 2.3).
-- 
--  1. Initialize state from key, nonce, and counter.
--  2. Copy the initial state.
--  3. Run 20 rounds (10 double rounds) on the working state.
--  4. Add the initial state to the working state (wrapping_add per word).
--  5. Serialize the 16 u32 words as 64 little-endian bytes.
def chacha20_block
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (counter : u32) :
    RustM (RustArray u8 64) := do
  let initial_state : (RustArray u32 16) ← (chacha20_init key nonce counter);
  let working_state : (RustArray u32 16) := initial_state;
  let working_state : (RustArray u32 16) ← (chacha20_inner_block working_state);
  let working_state : (RustArray u32 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun working_state _ => (do (pure true) : RustM Bool))
      working_state
      (fun working_state i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          working_state
          i
          (← (Core_models.Num.Impl_8.wrapping_add
            (← working_state[i]_?)
            (← initial_state[i]_?)))) :
        RustM (RustArray u32 16))));
  let output : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let output : (RustArray u8 64) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun output _ => (do (pure true) : RustM Bool))
      output
      (fun output i =>
        (do
        (u32_to_le_bytes (← working_state[i]_?) output (← ((4 : usize) *? i))) :
        RustM (RustArray u8 64))));
  (pure output)

--  Encrypt (or decrypt) a message using ChaCha20 (RFC 8439, Section 2.4).
-- 
--  Generates keystream blocks starting at `counter`, XORs them with the
--  message. Encryption and decryption are the same operation (XOR is
--  its own inverse).
def chacha20_encrypt
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (counter : u32)
    (msg : (RustSlice u8)) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8 (← (Core_models.Slice.Impl.len u8 msg)));
  let num_full_blocks : usize ←
    ((← (Core_models.Slice.Impl.len u8 msg)) /? (64 : usize));
  let remainder : usize ←
    ((← (Core_models.Slice.Impl.len u8 msg)) %? (64 : usize));
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_full_blocks
      (fun output _ => (do (pure true) : RustM Bool))
      output
      (fun output i =>
        (do
        let block : (RustArray u8 64) ←
          (chacha20_block
            key
            nonce
            (← (Core_models.Num.Impl_8.wrapping_add
              counter
              (← (Rust_primitives.Hax.cast_op i)))));
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (64 : usize)
          (fun output _ => (do (pure true) : RustM Bool))
          output
          (fun output j =>
            (do
            (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
              output
              (← ((← msg[(← ((← (i *? (64 : usize))) +? j))]_?)
                ^^^? (← block[j]_?)))) :
            RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let output : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    if (← (Rust_primitives.Hax.Machine_int.gt remainder (0 : usize))) then
      let block : (RustArray u8 64) ←
        (chacha20_block
          key
          nonce
          (← (Core_models.Num.Impl_8.wrapping_add
            counter
            (← (Rust_primitives.Hax.cast_op num_full_blocks)))));
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        remainder
        (fun output _ => (do (pure true) : RustM Bool))
        output
        (fun output j =>
          (do
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            output
            (← ((← msg[(← ((← (num_full_blocks *? (64 : usize))) +? j))]_?)
              ^^^? (← block[j]_?)))) :
          RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))))
    else
      (pure output);
  (pure output)

end Libcrux_specs_hax.Chacha20


namespace Libcrux_specs_hax.Poly1305

--  A 130-bit number represented as (low 128 bits, high 2 bits).
--  Value = lo + (hi as u128) * 2^128.
--  hi is at most 7 (3 bits) before reduction, at most 3 (2 bits) after.
structure U130 where
  lo : u128
  hi : u8

@[instance] opaque Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes U130 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  Core_models.Clone.Clone U130 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes U130 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Marker.Copy U130 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Fmt.Debug.AssociatedTypes U130 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Fmt.Debug U130 :=
  by constructor <;> exact Inhabited.default

--  A 256-bit number represented as two u128 halves.
--  Value = lo + hi * 2^128.
structure U256 where
  lo : u128
  hi : u128

@[instance] opaque Impl_3.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes U256 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_3 :
  Core_models.Clone.Clone U256 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes U256 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_4 :
  Core_models.Marker.Copy U256 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5.AssociatedTypes :
  Core_models.Fmt.Debug.AssociatedTypes U256 :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_5 :
  Core_models.Fmt.Debug U256 :=
  by constructor <;> exact Inhabited.default

--  The prime modulus p = 2^130 - 5.
--  We store this symbolically and reduce using the identity: 2^130 = 5 (mod p).
def P_LO : u128 :=
  RustM.of_isOk (do (Core_models.Num.Impl_10.MAX -? (4 : u128))) (by rfl)

def P_HI : u8 := (3 : u8)

--  Clamp the r value per RFC 8439, Section 2.5.
-- 
--  Certain bits of r must be cleared to ensure the key is in the correct form:
--  - Clear top 4 bits of bytes 3, 7, 11, 15 (i.e., r[3], r[7], r[11], r[15] &= 0x0f)
--  - Clear bottom 2 bits of bytes 4, 8, 12 (i.e., r[4], r[8], r[12] &= 0xfc)
def poly1305_clamp (r : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let clamped : (RustArray u8 16) := r;
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (3 : usize)
      (← ((← clamped[(3 : usize)]_?) &&&? (15 : u8))));
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (7 : usize)
      (← ((← clamped[(7 : usize)]_?) &&&? (15 : u8))));
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (11 : usize)
      (← ((← clamped[(11 : usize)]_?) &&&? (15 : u8))));
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (15 : usize)
      (← ((← clamped[(15 : usize)]_?) &&&? (15 : u8))));
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (4 : usize)
      (← ((← clamped[(4 : usize)]_?) &&&? (252 : u8))));
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (8 : usize)
      (← ((← clamped[(8 : usize)]_?) &&&? (252 : u8))));
  let clamped : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      clamped
      (12 : usize)
      (← ((← clamped[(12 : usize)]_?) &&&? (252 : u8))));
  (pure clamped)

--  Decode a little-endian byte slice (up to 17 bytes) into a U130.
-- 
--  For Poly1305, this handles blocks up to 16 bytes plus the "high bit"
--  (2^(8*len)) which makes the result up to 129 bits.
def le_bytes_to_u130 (bytes : (RustSlice u8)) : RustM U130 := do
  let lo : u128 := (0 : u128);
  let hi : u8 := (0 : u8);
  let ⟨hi, lo⟩ ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core_models.Slice.Impl.len u8 bytes))
      (fun ⟨hi, lo⟩ _ => (do (pure true) : RustM Bool))
      (Rust_primitives.Hax.Tuple2.mk hi lo)
      (fun ⟨hi, lo⟩ i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i (16 : usize))) then
          let lo : u128 ←
            (Rust_primitives.Hax.Machine_int.bitor
              lo
              (← ((← (Rust_primitives.Hax.cast_op (← bytes[i]_?)))
                <<<? (← ((8 : usize) *? i)))));
          (pure (Rust_primitives.Hax.Tuple2.mk hi lo))
        else
          let hi : u8 ←
            (Rust_primitives.Hax.Machine_int.bitor hi (← bytes[i]_?));
          (pure (Rust_primitives.Hax.Tuple2.mk hi lo)) :
        RustM (Rust_primitives.Hax.Tuple2 u8 u128))));
  (pure (U130.mk (lo := lo) (hi := hi)))

--  Decode a little-endian byte slice (up to 16 bytes) into a u128.
def le_bytes_to_num (bytes : (RustSlice u8)) : RustM u128 := do
  let result : u128 := (0 : u128);
  let result : u128 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core_models.Slice.Impl.len u8 bytes))
      (fun result _ => (do (pure true) : RustM Bool))
      result
      (fun result i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt i (16 : usize))) then
          let result : u128 ←
            (Rust_primitives.Hax.Machine_int.bitor
              result
              (← ((← (Rust_primitives.Hax.cast_op (← bytes[i]_?)))
                <<<? (← ((8 : usize) *? i)))));
          (pure result)
        else
          (pure result) :
        RustM u128)));
  (pure result)

--  Encode a u128 as 16 little-endian bytes.
def num_to_le_bytes (value : u128) : RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← (Rust_primitives.Hax.cast_op
            (← (value >>>? (← ((8 : usize) *? i))))))) :
        RustM (RustArray u8 16))));
  (pure out)

--  Add a U130 value to the accumulator.
--  Result may have hi up to 7 (3 bits).
def u130_add (a : U130) (b : U130) : RustM U130 := do
  let ⟨lo, carry⟩ ←
    (Core_models.Num.Impl_10.overflowing_add (U130.lo a) (U130.lo b));
  let hi : u8 ←
    ((← ((U130.hi a) +? (U130.hi b)))
      +? (← (Rust_primitives.Hax.cast_op carry)));
  (pure (U130.mk (lo := lo) (hi := hi)))

--  Multiply two u128 values, returning a U256 (256-bit result).
-- 
--  Uses schoolbook multiplication with 64-bit limbs:
--  a = a_lo + a_hi * 2^64
--  b = b_lo + b_hi * 2^64
--  a*b = a_lo*b_lo + (a_lo*b_hi + a_hi*b_lo)*2^64 + a_hi*b_hi*2^128
def u128_mul (a : u128) (b : u128) : RustM U256 := do
  let a_lo : u128 ←
    (Rust_primitives.Hax.cast_op (← (Rust_primitives.Hax.cast_op a)));
  let a_hi : u128 ←
    (Rust_primitives.Hax.cast_op
      (← (Rust_primitives.Hax.cast_op (← (a >>>? (64 : i32))))));
  let b_lo : u128 ←
    (Rust_primitives.Hax.cast_op (← (Rust_primitives.Hax.cast_op b)));
  let b_hi : u128 ←
    (Rust_primitives.Hax.cast_op
      (← (Rust_primitives.Hax.cast_op (← (b >>>? (64 : i32))))));
  let ll : u128 ← (a_lo *? b_lo);
  let lh : u128 ← (a_lo *? b_hi);
  let hl : u128 ← (a_hi *? b_lo);
  let hh : u128 ← (a_hi *? b_hi);
  let ⟨mid_sum, mid_carry⟩ ← (Core_models.Num.Impl_10.overflowing_add lh hl);
  let mid_lo : u128 ←
    ((← (Rust_primitives.Hax.cast_op (← (Rust_primitives.Hax.cast_op mid_sum))))
      <<<? (64 : i32));
  let mid_hi : u128 ←
    (Rust_primitives.Hax.cast_op
      (← (Rust_primitives.Hax.cast_op (← (mid_sum >>>? (64 : i32))))));
  let ⟨lo, carry1⟩ ← (Core_models.Num.Impl_10.overflowing_add ll mid_lo);
  let hi : u128 ←
    (Core_models.Num.Impl_10.wrapping_add
      (← (Core_models.Num.Impl_10.wrapping_add
        (← (Core_models.Num.Impl_10.wrapping_add hh mid_hi))
        (← (Rust_primitives.Hax.cast_op carry1))))
      (← if mid_carry then
        ((1 : u128) <<<? (64 : i32))
      else
        (pure (0 : u128))));
  (pure (U256.mk (lo := lo) (hi := hi)))

--  Multiply a U130 accumulator by a u128 r value, returning up to 258 bits.
-- 
--  acc = acc_lo + acc_hi * 2^128   (acc_hi <= 7)
--  r is at most 124 bits (after clamping)
-- 
--  result = acc_lo * r + acc_hi * r * 2^128
-- 
--  Then reduce modulo 2^130 - 5.
def u130_mul_mod (acc : U130) (r : u128) : RustM U130 := do
  let prod_lo : U256 ← (u128_mul (U130.lo acc) r);
  let prod_hi_val : u128 ←
    ((← (Rust_primitives.Hax.cast_op (U130.hi acc))) *? r);
  let ⟨upper, carry⟩ ←
    (Core_models.Num.Impl_10.overflowing_add (U256.hi prod_lo) prod_hi_val);
  let upper_lo2 : u8 ←
    (Rust_primitives.Hax.cast_op (← (upper &&&? (3 : u128))));
  let upper_hi : u128 ← (upper >>>? (2 : i32));
  let base_lo : u128 := (U256.lo prod_lo);
  let base_hi : u8 := upper_lo2;
  let high_times_5 : u128 ←
    (Core_models.Num.Impl_10.wrapping_add
      (← (Core_models.Num.Impl_10.wrapping_mul upper_hi (5 : u128)))
      (← if carry then ((5 : u128) <<<? (126 : i32)) else (pure (0 : u128))));
  let ⟨sum_lo, c⟩ ←
    (Core_models.Num.Impl_10.overflowing_add base_lo high_times_5);
  let sum_hi : u8 ← (base_hi +? (← (Rust_primitives.Hax.cast_op c)));
  let extra : u8 ← (sum_hi >>>? (2 : i32));
  let final_hi : u8 ← (sum_hi &&&? (3 : u8));
  let ⟨final_lo, c2⟩ ←
    (Core_models.Num.Impl_10.overflowing_add
      sum_lo
      (← ((← (Rust_primitives.Hax.cast_op extra)) *? (5 : u128))));
  let final_hi2 : u8 ← (final_hi +? (← (Rust_primitives.Hax.cast_op c2)));
  (pure (U130.mk (lo := final_lo) (hi := final_hi2)))

--  Final reduction: ensure value is in [0, 2^130-5).
-- 
--  After all block processing, the accumulator is at most slightly above p.
--  We check if acc >= p, and if so subtract p.
def final_reduce (acc : U130) : RustM u128 := do
  let ⟨test_lo, c⟩ ←
    (Core_models.Num.Impl_10.overflowing_add (U130.lo acc) (5 : u128));
  let test_hi : u8 ← ((U130.hi acc) +? (← (Rust_primitives.Hax.cast_op c)));
  if (← (Rust_primitives.Hax.Machine_int.ge test_hi (4 : u8))) then
    (pure test_lo)
  else
    (pure (U130.lo acc))

--  Compute the Poly1305 MAC tag (RFC 8439, Section 2.5.1).
-- 
--  1. Split key into r (first 16 bytes, clamped) and s (last 16 bytes).
--  2. Process each 16-byte block: add high bit, accumulate (acc + n) * r mod p.
--  3. Final tag = (acc + s) mod 2^128, as 16 little-endian bytes.
def poly1305 (msg : (RustSlice u8)) (key : (RustArray u8 32)) :
    RustM (RustArray u8 16) := do
  let r_bytes : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let r_bytes : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun r_bytes _ => (do (pure true) : RustM Bool))
      r_bytes
      (fun r_bytes i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          r_bytes
          i
          (← key[i]_?)) :
        RustM (RustArray u8 16))));
  let r_bytes : (RustArray u8 16) ← (poly1305_clamp r_bytes);
  let r : u128 ← (le_bytes_to_num (← (Rust_primitives.unsize r_bytes)));
  let s_bytes : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let s_bytes : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun s_bytes _ => (do (pure true) : RustM Bool))
      s_bytes
      (fun s_bytes i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          s_bytes
          i
          (← key[(← ((16 : usize) +? i))]_?)) :
        RustM (RustArray u8 16))));
  let s : u128 ← (le_bytes_to_num (← (Rust_primitives.unsize s_bytes)));
  let acc : U130 := (U130.mk (lo := (0 : u128)) (hi := (0 : u8)));
  let num_full_blocks : usize ←
    ((← (Core_models.Slice.Impl.len u8 msg)) /? (16 : usize));
  let acc : U130 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      num_full_blocks
      (fun acc _ => (do (pure true) : RustM Bool))
      acc
      (fun acc i =>
        (do
        let block : (RustArray u8 16) ←
          (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
        let block : (RustArray u8 16) ←
          (Rust_primitives.Hax.Folds.fold_range
            (0 : usize)
            (16 : usize)
            (fun block _ => (do (pure true) : RustM Bool))
            block
            (fun block j =>
              (do
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                block
                j
                (← msg[(← ((← (i *? (16 : usize))) +? j))]_?)) :
              RustM (RustArray u8 16))));
        let n : U130 :=
          (U130.mk
            (lo := (← (le_bytes_to_num (← (Rust_primitives.unsize block)))))
            (hi := (1 : u8)));
        let acc : U130 ← (u130_add acc n);
        let acc : U130 ← (u130_mul_mod acc r);
        (pure acc) :
        RustM U130)));
  let remainder : usize ←
    ((← (Core_models.Slice.Impl.len u8 msg)) %? (16 : usize));
  let acc : U130 ←
    if (← (Rust_primitives.Hax.Machine_int.gt remainder (0 : usize))) then
      let offset : usize ← (num_full_blocks *? (16 : usize));
      let block : (RustArray u8 17) ←
        (Rust_primitives.Hax.repeat (0 : u8) (17 : usize));
      let block : (RustArray u8 17) ←
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          remainder
          (fun block _ => (do (pure true) : RustM Bool))
          block
          (fun block j =>
            (do
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              block
              j
              (← msg[(← (offset +? j))]_?)) :
            RustM (RustArray u8 17))));
      let block : (RustArray u8 17) ←
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          block
          remainder
          (1 : u8));
      let n : U130 ←
        (le_bytes_to_u130
          (← block[
            (Core_models.Ops.Range.RangeTo.mk
              (_end := (← (remainder +? (1 : usize)))))
            ]_?));
      let acc : U130 ← (u130_add acc n);
      let acc : U130 ← (u130_mul_mod acc r);
      (pure acc)
    else
      (pure acc);
  let acc_reduced : u128 ← (final_reduce acc);
  let tag_full : u128 ← (Core_models.Num.Impl_10.wrapping_add acc_reduced s);
  (num_to_le_bytes tag_full)

end Libcrux_specs_hax.Poly1305


namespace Libcrux_specs_hax.Chacha20poly1305

--  Pad data to a multiple of 16 bytes by appending zeros.
--  Returns the data followed by 0 to 15 zero bytes.
def pad16 (data : (RustSlice u8)) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let padded : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8
      (← ((← (Core_models.Slice.Impl.len u8 data)) +? (15 : usize))));
  let padded : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Core_models.Slice.Impl.len u8 data))
      (fun padded _ => (do (pure true) : RustM Bool))
      padded
      (fun padded i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global padded (← data[i]_?)) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let remainder : usize ←
    ((← (Core_models.Slice.Impl.len u8 data)) %? (16 : usize));
  let padded : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    if (← (Rust_primitives.Hax.Machine_int.ne remainder (0 : usize))) then
      let pad_len : usize ← ((16 : usize) -? remainder);
      (Rust_primitives.Hax.Folds.fold_range
        (0 : usize)
        pad_len
        (fun padded _ => (do (pure true) : RustM Bool))
        padded
        (fun padded _ =>
          (do
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global padded (0 : u8)) :
          RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))))
    else
      (pure padded);
  (pure padded)

--  Encode a usize as 8 little-endian bytes (u64).
def le64 (value : usize) : RustM (RustArray u8 8) := do
  let v : u64 ← (Rust_primitives.Hax.cast_op value);
  let out : (RustArray u8 8) ←
    (Rust_primitives.Hax.repeat (0 : u8) (8 : usize));
  let out : (RustArray u8 8) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← (Rust_primitives.Hax.cast_op (← (v >>>? (← ((8 : usize) *? i)))))))
        :
        RustM (RustArray u8 8))));
  (pure out)

--  Build the Poly1305 MAC input for AEAD (RFC 8439, Section 2.8).
-- 
--  ```text
--  mac_data = pad16(aad) || pad16(ciphertext) || le64(aad.len()) || le64(ciphertext.len())
--  ```
def build_mac_data (aad : (RustSlice u8)) (ciphertext : (RustSlice u8)) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let padded_aad : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pad16 aad);
  let padded_ct : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ← (pad16 ciphertext);
  let aad_len : (RustArray u8 8) ←
    (le64 (← (Core_models.Slice.Impl.len u8 aad)));
  let ct_len : (RustArray u8 8) ←
    (le64 (← (Core_models.Slice.Impl.len u8 ciphertext)));
  let total_len : usize ←
    ((← ((← ((← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global padded_aad))
          +? (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global padded_ct))))
        +? (8 : usize)))
      +? (8 : usize));
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.with_capacity u8 total_len);
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global padded_aad))
      (fun mac_data _ => (do (pure true) : RustM Bool))
      mac_data
      (fun mac_data i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
          mac_data
          (← padded_aad[i]_?)) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global padded_ct))
      (fun mac_data _ => (do (pure true) : RustM Bool))
      mac_data
      (fun mac_data i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
          mac_data
          (← padded_ct[i]_?)) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun mac_data _ => (do (pure true) : RustM Bool))
      mac_data
      (fun mac_data i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global mac_data (← aad_len[i]_?))
        :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (8 : usize)
      (fun mac_data _ => (do (pure true) : RustM Bool))
      mac_data
      (fun mac_data i =>
        (do
        (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global mac_data (← ct_len[i]_?)) :
        RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global))));
  (pure mac_data)

--  Generate the one-time Poly1305 key from ChaCha20 block 0.
-- 
--  The first 32 bytes of chacha20_block(key, nonce, 0) are used as the
--  Poly1305 key (RFC 8439, Section 2.6).
def poly1305_key_gen (key : (RustArray u8 32)) (nonce : (RustArray u8 12)) :
    RustM (RustArray u8 32) := do
  let block : (RustArray u8 64) ←
    (Libcrux_specs_hax.Chacha20.chacha20_block key nonce (0 : u32));
  let poly_key : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let poly_key : (RustArray u8 32) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (32 : usize)
      (fun poly_key _ => (do (pure true) : RustM Bool))
      poly_key
      (fun poly_key i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          poly_key
          i
          (← block[i]_?)) :
        RustM (RustArray u8 32))));
  (pure poly_key)

--  Constant-time comparison of two 16-byte tags.
-- 
--  Returns true if and only if all bytes are equal. Evaluates all bytes
--  regardless of where a mismatch occurs.
def constant_time_eq (a : (RustArray u8 16)) (b : (RustArray u8 16)) :
    RustM Bool := do
  let diff : u8 := (0 : u8);
  let diff : u8 ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun diff _ => (do (pure true) : RustM Bool))
      diff
      (fun diff i =>
        (do
        (Rust_primitives.Hax.Machine_int.bitor
          diff
          (← ((← a[i]_?) ^^^? (← b[i]_?)))) :
        RustM u8)));
  (Rust_primitives.Hax.Machine_int.eq diff (0 : u8))

--  Encrypt and authenticate with ChaCha20-Poly1305 (RFC 8439, Section 2.8).
-- 
--  1. Generate one-time Poly1305 key from ChaCha20 block 0.
--  2. Encrypt plaintext with ChaCha20 starting at counter 1.
--  3. Compute Poly1305 tag over pad16(aad) || pad16(ciphertext) || le64(aad_len) || le64(ct_len).
-- 
--  Returns (ciphertext, tag).
def chacha20_poly1305_encrypt
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (msg : (RustSlice u8)) :
    RustM
    (Rust_primitives.Hax.Tuple2
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      (RustArray u8 16))
    := do
  let poly_key : (RustArray u8 32) ← (poly1305_key_gen key nonce);
  let ciphertext : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Libcrux_specs_hax.Chacha20.chacha20_encrypt key nonce (1 : u32) msg);
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (build_mac_data
      aad
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ciphertext)));
  let tag : (RustArray u8 16) ←
    (Libcrux_specs_hax.Poly1305.poly1305
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) mac_data))
      poly_key);
  (pure (Rust_primitives.Hax.Tuple2.mk ciphertext tag))

--  Decrypt and verify with ChaCha20-Poly1305 (RFC 8439, Section 2.8).
-- 
--  1. Generate one-time Poly1305 key from ChaCha20 block 0.
--  2. Recompute Poly1305 tag over pad16(aad) || pad16(ciphertext) || le64(aad_len) || le64(ct_len).
--  3. If tag matches, decrypt ciphertext with ChaCha20 starting at counter 1.
-- 
--  Returns `Some(plaintext)` on success, `None` if authentication fails.
def chacha20_poly1305_decrypt
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (ciphertext : (RustSlice u8))
    (tag : (RustArray u8 16)) :
    RustM
    (Core_models.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    := do
  let poly_key : (RustArray u8 32) ← (poly1305_key_gen key nonce);
  let mac_data : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (build_mac_data aad ciphertext);
  let computed_tag : (RustArray u8 16) ←
    (Libcrux_specs_hax.Poly1305.poly1305
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) mac_data))
      poly_key);
  if (← (constant_time_eq computed_tag tag)) then
    let plaintext : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
      (Libcrux_specs_hax.Chacha20.chacha20_encrypt
        key
        nonce
        (1 : u32)
        ciphertext);
    (pure (Core_models.Option.Option.Some plaintext))
  else
    (pure Core_models.Option.Option.None)

end Libcrux_specs_hax.Chacha20poly1305


namespace Libcrux_specs_hax.Aes128

def SBOX : (RustArray u8 256) :=
  RustM.of_isOk
    (do
    #v[(99 : u8),
         (124 : u8),
         (119 : u8),
         (123 : u8),
         (242 : u8),
         (107 : u8),
         (111 : u8),
         (197 : u8),
         (48 : u8),
         (1 : u8),
         (103 : u8),
         (43 : u8),
         (254 : u8),
         (215 : u8),
         (171 : u8),
         (118 : u8),
         (202 : u8),
         (130 : u8),
         (201 : u8),
         (125 : u8),
         (250 : u8),
         (89 : u8),
         (71 : u8),
         (240 : u8),
         (173 : u8),
         (212 : u8),
         (162 : u8),
         (175 : u8),
         (156 : u8),
         (164 : u8),
         (114 : u8),
         (192 : u8),
         (183 : u8),
         (253 : u8),
         (147 : u8),
         (38 : u8),
         (54 : u8),
         (63 : u8),
         (247 : u8),
         (204 : u8),
         (52 : u8),
         (165 : u8),
         (229 : u8),
         (241 : u8),
         (113 : u8),
         (216 : u8),
         (49 : u8),
         (21 : u8),
         (4 : u8),
         (199 : u8),
         (35 : u8),
         (195 : u8),
         (24 : u8),
         (150 : u8),
         (5 : u8),
         (154 : u8),
         (7 : u8),
         (18 : u8),
         (128 : u8),
         (226 : u8),
         (235 : u8),
         (39 : u8),
         (178 : u8),
         (117 : u8),
         (9 : u8),
         (131 : u8),
         (44 : u8),
         (26 : u8),
         (27 : u8),
         (110 : u8),
         (90 : u8),
         (160 : u8),
         (82 : u8),
         (59 : u8),
         (214 : u8),
         (179 : u8),
         (41 : u8),
         (227 : u8),
         (47 : u8),
         (132 : u8),
         (83 : u8),
         (209 : u8),
         (0 : u8),
         (237 : u8),
         (32 : u8),
         (252 : u8),
         (177 : u8),
         (91 : u8),
         (106 : u8),
         (203 : u8),
         (190 : u8),
         (57 : u8),
         (74 : u8),
         (76 : u8),
         (88 : u8),
         (207 : u8),
         (208 : u8),
         (239 : u8),
         (170 : u8),
         (251 : u8),
         (67 : u8),
         (77 : u8),
         (51 : u8),
         (133 : u8),
         (69 : u8),
         (249 : u8),
         (2 : u8),
         (127 : u8),
         (80 : u8),
         (60 : u8),
         (159 : u8),
         (168 : u8),
         (81 : u8),
         (163 : u8),
         (64 : u8),
         (143 : u8),
         (146 : u8),
         (157 : u8),
         (56 : u8),
         (245 : u8),
         (188 : u8),
         (182 : u8),
         (218 : u8),
         (33 : u8),
         (16 : u8),
         (255 : u8),
         (243 : u8),
         (210 : u8),
         (205 : u8),
         (12 : u8),
         (19 : u8),
         (236 : u8),
         (95 : u8),
         (151 : u8),
         (68 : u8),
         (23 : u8),
         (196 : u8),
         (167 : u8),
         (126 : u8),
         (61 : u8),
         (100 : u8),
         (93 : u8),
         (25 : u8),
         (115 : u8),
         (96 : u8),
         (129 : u8),
         (79 : u8),
         (220 : u8),
         (34 : u8),
         (42 : u8),
         (144 : u8),
         (136 : u8),
         (70 : u8),
         (238 : u8),
         (184 : u8),
         (20 : u8),
         (222 : u8),
         (94 : u8),
         (11 : u8),
         (219 : u8),
         (224 : u8),
         (50 : u8),
         (58 : u8),
         (10 : u8),
         (73 : u8),
         (6 : u8),
         (36 : u8),
         (92 : u8),
         (194 : u8),
         (211 : u8),
         (172 : u8),
         (98 : u8),
         (145 : u8),
         (149 : u8),
         (228 : u8),
         (121 : u8),
         (231 : u8),
         (200 : u8),
         (55 : u8),
         (109 : u8),
         (141 : u8),
         (213 : u8),
         (78 : u8),
         (169 : u8),
         (108 : u8),
         (86 : u8),
         (244 : u8),
         (234 : u8),
         (101 : u8),
         (122 : u8),
         (174 : u8),
         (8 : u8),
         (186 : u8),
         (120 : u8),
         (37 : u8),
         (46 : u8),
         (28 : u8),
         (166 : u8),
         (180 : u8),
         (198 : u8),
         (232 : u8),
         (221 : u8),
         (116 : u8),
         (31 : u8),
         (75 : u8),
         (189 : u8),
         (139 : u8),
         (138 : u8),
         (112 : u8),
         (62 : u8),
         (181 : u8),
         (102 : u8),
         (72 : u8),
         (3 : u8),
         (246 : u8),
         (14 : u8),
         (97 : u8),
         (53 : u8),
         (87 : u8),
         (185 : u8),
         (134 : u8),
         (193 : u8),
         (29 : u8),
         (158 : u8),
         (225 : u8),
         (248 : u8),
         (152 : u8),
         (17 : u8),
         (105 : u8),
         (217 : u8),
         (142 : u8),
         (148 : u8),
         (155 : u8),
         (30 : u8),
         (135 : u8),
         (233 : u8),
         (206 : u8),
         (85 : u8),
         (40 : u8),
         (223 : u8),
         (140 : u8),
         (161 : u8),
         (137 : u8),
         (13 : u8),
         (191 : u8),
         (230 : u8),
         (66 : u8),
         (104 : u8),
         (65 : u8),
         (153 : u8),
         (45 : u8),
         (15 : u8),
         (176 : u8),
         (84 : u8),
         (187 : u8),
         (22 : u8)])
    (by rfl)

def RCON : (RustArray u8 10) :=
  RustM.of_isOk
    (do
    #v[(1 : u8),
         (2 : u8),
         (4 : u8),
         (8 : u8),
         (16 : u8),
         (32 : u8),
         (64 : u8),
         (128 : u8),
         (27 : u8),
         (54 : u8)])
    (by rfl)

def gf_mul2 (x : u8) : RustM u8 := do
  let s : u16 ← ((← (Rust_primitives.Hax.cast_op x)) <<<? (1 : i32));
  if (← (Rust_primitives.Hax.Machine_int.ge s (256 : u16))) then
    (Rust_primitives.Hax.cast_op (← (s ^^^? (283 : u16))))
  else
    (Rust_primitives.Hax.cast_op s)

def sub_bytes (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← SBOX[(← (Rust_primitives.Hax.cast_op (← state[i]_?)))]_?)) :
        RustM (RustArray u8 16))));
  (pure out)

def shift_rows (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (4 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out col =>
        (do
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (4 : usize)
          (fun out _ => (do (pure true) : RustM Bool))
          out
          (fun out row =>
            (do
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              (← (row +? (← ((4 : usize) *? col))))
              (← state[
                (← (row
                  +? (← ((4 : usize)
                    *? (← ((← (col +? row)) %? (4 : usize)))))))
                ]_?)) :
            RustM (RustArray u8 16)))) :
        RustM (RustArray u8 16))));
  (pure out)

def mix_columns (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (4 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out col =>
        (do
        let ⟨s0, s1, s2, s3⟩ :=
          (Rust_primitives.Hax.Tuple4.mk
            (← state[(← ((4 : usize) *? col))]_?)
            (← state[(← ((← ((4 : usize) *? col)) +? (1 : usize)))]_?)
            (← state[(← ((← ((4 : usize) *? col)) +? (2 : usize)))]_?)
            (← state[(← ((← ((4 : usize) *? col)) +? (3 : usize)))]_?));
        let out : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            out
            (← ((4 : usize) *? col))
            (← ((← ((← ((← ((← (gf_mul2 s0)) ^^^? (← (gf_mul2 s1)))) ^^^? s1))
                ^^^? s2))
              ^^^? s3)));
        let out : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            out
            (← ((← ((4 : usize) *? col)) +? (1 : usize)))
            (← ((← ((← ((← (s0 ^^^? (← (gf_mul2 s1)))) ^^^? (← (gf_mul2 s2))))
                ^^^? s2))
              ^^^? s3)));
        let out : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            out
            (← ((← ((4 : usize) *? col)) +? (2 : usize)))
            (← ((← ((← ((← (s0 ^^^? s1)) ^^^? (← (gf_mul2 s2))))
                ^^^? (← (gf_mul2 s3))))
              ^^^? s3)));
        let out : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            out
            (← ((← ((4 : usize) *? col)) +? (3 : usize)))
            (← ((← ((← ((← ((← (gf_mul2 s0)) ^^^? s0)) ^^^? s1)) ^^^? s2))
              ^^^? (← (gf_mul2 s3)))));
        (pure out) :
        RustM (RustArray u8 16))));
  (pure out)

def add_round_key (state : (RustArray u8 16)) (key : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let out : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (16 : usize)
      (fun out _ => (do (pure true) : RustM Bool))
      out
      (fun out i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          out
          i
          (← ((← state[i]_?) ^^^? (← key[i]_?)))) :
        RustM (RustArray u8 16))));
  (pure out)

def key_expansion (key : (RustArray u8 16)) :
    RustM (RustArray (RustArray u8 16) 11) := do
  let w : (RustArray (RustArray u8 4) 44) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (4 : usize)))
      (44 : usize));
  let w : (RustArray (RustArray u8 4) 44) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (4 : usize)
      (fun w _ => (do (pure true) : RustM Bool))
      w
      (fun w i =>
        (do
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          w
          i
          #v[(← key[(← ((4 : usize) *? i))]_?),
               (← key[(← ((← ((4 : usize) *? i)) +? (1 : usize)))]_?),
               (← key[(← ((← ((4 : usize) *? i)) +? (2 : usize)))]_?),
               (← key[(← ((← ((4 : usize) *? i)) +? (3 : usize)))]_?)]) :
        RustM (RustArray (RustArray u8 4) 44))));
  let w : (RustArray (RustArray u8 4) 44) ←
    (Rust_primitives.Hax.Folds.fold_range
      (4 : usize)
      (44 : usize)
      (fun w _ => (do (pure true) : RustM Bool))
      w
      (fun w i =>
        (do
        let temp : (RustArray u8 4) ← w[(← (i -? (1 : usize)))]_?;
        let temp : (RustArray u8 4) ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← (i %? (4 : usize)))
            (0 : usize))) then
            let t : u8 ← temp[(0 : usize)]_?;
            let temp : (RustArray u8 4) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                temp
                (0 : usize)
                (← ((← SBOX[
                    (← (Rust_primitives.Hax.cast_op (← temp[(1 : usize)]_?)))
                    ]_?)
                  ^^^? (← RCON[
                    (← ((← (i /? (4 : usize))) -? (1 : usize)))
                    ]_?))));
            let temp : (RustArray u8 4) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                temp
                (1 : usize)
                (← SBOX[
                  (← (Rust_primitives.Hax.cast_op (← temp[(2 : usize)]_?)))
                  ]_?));
            let temp : (RustArray u8 4) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                temp
                (2 : usize)
                (← SBOX[
                  (← (Rust_primitives.Hax.cast_op (← temp[(3 : usize)]_?)))
                  ]_?));
            let temp : (RustArray u8 4) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                temp
                (3 : usize)
                (← SBOX[(← (Rust_primitives.Hax.cast_op t))]_?));
            (pure temp)
          else
            (pure temp);
        let w : (RustArray (RustArray u8 4) 44) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            i
            #v[(← ((← (← w[(← (i -? (4 : usize)))]_?)[(0 : usize)]_?)
                   ^^^? (← temp[(0 : usize)]_?))),
                 (← ((← (← w[(← (i -? (4 : usize)))]_?)[(1 : usize)]_?)
                   ^^^? (← temp[(1 : usize)]_?))),
                 (← ((← (← w[(← (i -? (4 : usize)))]_?)[(2 : usize)]_?)
                   ^^^? (← temp[(2 : usize)]_?))),
                 (← ((← (← w[(← (i -? (4 : usize)))]_?)[(3 : usize)]_?)
                   ^^^? (← temp[(3 : usize)]_?)))]);
        (pure w) :
        RustM (RustArray (RustArray u8 4) 44))));
  let rk : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (11 : usize));
  let rk : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.Folds.fold_range
      (0 : usize)
      (11 : usize)
      (fun rk _ => (do (pure true) : RustM Bool))
      rk
      (fun rk r =>
        (do
        (Rust_primitives.Hax.Folds.fold_range
          (0 : usize)
          (4 : usize)
          (fun rk _ => (do (pure true) : RustM Bool))
          rk
          (fun rk j =>
            (do
            let rk : (RustArray (RustArray u8 16) 11) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                rk
                r
                (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  (← rk[r]_?)
                  (← ((4 : usize) *? j))
                  (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                    (0 : usize)
                    ]_?))));
            let rk : (RustArray (RustArray u8 16) 11) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                rk
                r
                (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  (← rk[r]_?)
                  (← ((← ((4 : usize) *? j)) +? (1 : usize)))
                  (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                    (1 : usize)
                    ]_?))));
            let rk : (RustArray (RustArray u8 16) 11) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                rk
                r
                (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  (← rk[r]_?)
                  (← ((← ((4 : usize) *? j)) +? (2 : usize)))
                  (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                    (2 : usize)
                    ]_?))));
            let rk : (RustArray (RustArray u8 16) 11) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                rk
                r
                (← (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  (← rk[r]_?)
                  (← ((← ((4 : usize) *? j)) +? (3 : usize)))
                  (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                    (3 : usize)
                    ]_?))));
            (pure rk) :
            RustM (RustArray (RustArray u8 16) 11)))) :
        RustM (RustArray (RustArray u8 16) 11))));
  (pure rk)

--  AES-128 block encryption (FIPS 197).
def aes128_encrypt (key : (RustArray u8 16)) (block : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let rk : (RustArray (RustArray u8 16) 11) ← (key_expansion key);
  let state : (RustArray u8 16) ← (add_round_key block (← rk[(0 : usize)]_?));
  let state : (RustArray u8 16) ←
    (Rust_primitives.Hax.Folds.fold_range
      (1 : usize)
      (10 : usize)
      (fun state _ => (do (pure true) : RustM Bool))
      state
      (fun state round =>
        (do
        let state : (RustArray u8 16) ← (sub_bytes state);
        let state : (RustArray u8 16) ← (shift_rows state);
        let state : (RustArray u8 16) ← (mix_columns state);
        let state : (RustArray u8 16) ← (add_round_key state (← rk[round]_?));
        (pure state) :
        RustM (RustArray u8 16))));
  let state : (RustArray u8 16) ← (sub_bytes state);
  let state : (RustArray u8 16) ← (shift_rows state);
  (add_round_key state (← rk[(10 : usize)]_?))

end Libcrux_specs_hax.Aes128


namespace Libcrux_specs_hax.Aes

--  AES S-box lookup table (FIPS 197, Section 5.1.1).
def SBOX : (RustArray u8 256) :=
  RustM.of_isOk
    (do
    #v[(99 : u8),
         (124 : u8),
         (119 : u8),
         (123 : u8),
         (242 : u8),
         (107 : u8),
         (111 : u8),
         (197 : u8),
         (48 : u8),
         (1 : u8),
         (103 : u8),
         (43 : u8),
         (254 : u8),
         (215 : u8),
         (171 : u8),
         (118 : u8),
         (202 : u8),
         (130 : u8),
         (201 : u8),
         (125 : u8),
         (250 : u8),
         (89 : u8),
         (71 : u8),
         (240 : u8),
         (173 : u8),
         (212 : u8),
         (162 : u8),
         (175 : u8),
         (156 : u8),
         (164 : u8),
         (114 : u8),
         (192 : u8),
         (183 : u8),
         (253 : u8),
         (147 : u8),
         (38 : u8),
         (54 : u8),
         (63 : u8),
         (247 : u8),
         (204 : u8),
         (52 : u8),
         (165 : u8),
         (229 : u8),
         (241 : u8),
         (113 : u8),
         (216 : u8),
         (49 : u8),
         (21 : u8),
         (4 : u8),
         (199 : u8),
         (35 : u8),
         (195 : u8),
         (24 : u8),
         (150 : u8),
         (5 : u8),
         (154 : u8),
         (7 : u8),
         (18 : u8),
         (128 : u8),
         (226 : u8),
         (235 : u8),
         (39 : u8),
         (178 : u8),
         (117 : u8),
         (9 : u8),
         (131 : u8),
         (44 : u8),
         (26 : u8),
         (27 : u8),
         (110 : u8),
         (90 : u8),
         (160 : u8),
         (82 : u8),
         (59 : u8),
         (214 : u8),
         (179 : u8),
         (41 : u8),
         (227 : u8),
         (47 : u8),
         (132 : u8),
         (83 : u8),
         (209 : u8),
         (0 : u8),
         (237 : u8),
         (32 : u8),
         (252 : u8),
         (177 : u8),
         (91 : u8),
         (106 : u8),
         (203 : u8),
         (190 : u8),
         (57 : u8),
         (74 : u8),
         (76 : u8),
         (88 : u8),
         (207 : u8),
         (208 : u8),
         (239 : u8),
         (170 : u8),
         (251 : u8),
         (67 : u8),
         (77 : u8),
         (51 : u8),
         (133 : u8),
         (69 : u8),
         (249 : u8),
         (2 : u8),
         (127 : u8),
         (80 : u8),
         (60 : u8),
         (159 : u8),
         (168 : u8),
         (81 : u8),
         (163 : u8),
         (64 : u8),
         (143 : u8),
         (146 : u8),
         (157 : u8),
         (56 : u8),
         (245 : u8),
         (188 : u8),
         (182 : u8),
         (218 : u8),
         (33 : u8),
         (16 : u8),
         (255 : u8),
         (243 : u8),
         (210 : u8),
         (205 : u8),
         (12 : u8),
         (19 : u8),
         (236 : u8),
         (95 : u8),
         (151 : u8),
         (68 : u8),
         (23 : u8),
         (196 : u8),
         (167 : u8),
         (126 : u8),
         (61 : u8),
         (100 : u8),
         (93 : u8),
         (25 : u8),
         (115 : u8),
         (96 : u8),
         (129 : u8),
         (79 : u8),
         (220 : u8),
         (34 : u8),
         (42 : u8),
         (144 : u8),
         (136 : u8),
         (70 : u8),
         (238 : u8),
         (184 : u8),
         (20 : u8),
         (222 : u8),
         (94 : u8),
         (11 : u8),
         (219 : u8),
         (224 : u8),
         (50 : u8),
         (58 : u8),
         (10 : u8),
         (73 : u8),
         (6 : u8),
         (36 : u8),
         (92 : u8),
         (194 : u8),
         (211 : u8),
         (172 : u8),
         (98 : u8),
         (145 : u8),
         (149 : u8),
         (228 : u8),
         (121 : u8),
         (231 : u8),
         (200 : u8),
         (55 : u8),
         (109 : u8),
         (141 : u8),
         (213 : u8),
         (78 : u8),
         (169 : u8),
         (108 : u8),
         (86 : u8),
         (244 : u8),
         (234 : u8),
         (101 : u8),
         (122 : u8),
         (174 : u8),
         (8 : u8),
         (186 : u8),
         (120 : u8),
         (37 : u8),
         (46 : u8),
         (28 : u8),
         (166 : u8),
         (180 : u8),
         (198 : u8),
         (232 : u8),
         (221 : u8),
         (116 : u8),
         (31 : u8),
         (75 : u8),
         (189 : u8),
         (139 : u8),
         (138 : u8),
         (112 : u8),
         (62 : u8),
         (181 : u8),
         (102 : u8),
         (72 : u8),
         (3 : u8),
         (246 : u8),
         (14 : u8),
         (97 : u8),
         (53 : u8),
         (87 : u8),
         (185 : u8),
         (134 : u8),
         (193 : u8),
         (29 : u8),
         (158 : u8),
         (225 : u8),
         (248 : u8),
         (152 : u8),
         (17 : u8),
         (105 : u8),
         (217 : u8),
         (142 : u8),
         (148 : u8),
         (155 : u8),
         (30 : u8),
         (135 : u8),
         (233 : u8),
         (206 : u8),
         (85 : u8),
         (40 : u8),
         (223 : u8),
         (140 : u8),
         (161 : u8),
         (137 : u8),
         (13 : u8),
         (191 : u8),
         (230 : u8),
         (66 : u8),
         (104 : u8),
         (65 : u8),
         (153 : u8),
         (45 : u8),
         (15 : u8),
         (176 : u8),
         (84 : u8),
         (187 : u8),
         (22 : u8)])
    (by rfl)

--  AES round constants (FIPS 197, Section 5.2).
def RCON : (RustArray u8 10) :=
  RustM.of_isOk
    (do
    #v[(1 : u8),
         (2 : u8),
         (4 : u8),
         (8 : u8),
         (16 : u8),
         (32 : u8),
         (64 : u8),
         (128 : u8),
         (27 : u8),
         (54 : u8)])
    (by rfl)

--  Multiply by 2 in GF(2^8) with irreducible polynomial x^8 + x^4 + x^3 + x + 1.
def gf_mul2 (x : u8) : RustM u8 := do
  let shifted : u16 ← ((← (Rust_primitives.Hax.cast_op x)) <<<? (1 : i32));
  if (← (Rust_primitives.Hax.Machine_int.ge shifted (256 : u16))) then
    (Rust_primitives.Hax.cast_op (← (shifted ^^^? (283 : u16))))
  else
    (Rust_primitives.Hax.cast_op shifted)

--  Multiply by 3 in GF(2^8): 3*x = 2*x XOR x.
def gf_mul3 (x : u8) : RustM u8 := do ((← (gf_mul2 x)) ^^^? x)

--  AES SubBytes: apply S-box to each byte of state.
def sub_bytes (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (16 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← SBOX[(← (Rust_primitives.Hax.cast_op (← state[i]_?)))]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  (pure result)

--  AES ShiftRows (FIPS 197, Section 5.1.2).
--  State is column-major: state[row + 4*col].
def shift_rows (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let col : usize := (0 : usize);
  let ⟨col, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨col, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨col, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt col (4 : usize)) : RustM Bool))
      (fun ⟨col, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk col result)
      (fun ⟨col, result⟩ =>
        (do
        let row : usize := (0 : usize);
        let ⟨result, row⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨result, row⟩ => (do (pure true) : RustM Bool))
            (fun ⟨result, row⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt row (4 : usize)) :
              RustM Bool))
            (fun ⟨result, row⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk result row)
            (fun ⟨result, row⟩ =>
              (do
              let result : (RustArray u8 16) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  result
                  (← (row +? (← ((4 : usize) *? col))))
                  (← state[
                    (← (row
                      +? (← ((4 : usize)
                        *? (← ((← (col +? row)) %? (4 : usize)))))))
                    ]_?));
              let row : usize ← (row +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk result row)) :
              RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) usize))));
        let col : usize ← (col +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk col result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  (pure result)

--  AES MixColumns (FIPS 197, Section 5.1.3).
def mix_columns (state : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let col : usize := (0 : usize);
  let ⟨col, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨col, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨col, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt col (4 : usize)) : RustM Bool))
      (fun ⟨col, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk col result)
      (fun ⟨col, result⟩ =>
        (do
        let s0 : u8 ← state[(← ((4 : usize) *? col))]_?;
        let s1 : u8 ← state[(← ((← ((4 : usize) *? col)) +? (1 : usize)))]_?;
        let s2 : u8 ← state[(← ((← ((4 : usize) *? col)) +? (2 : usize)))]_?;
        let s3 : u8 ← state[(← ((← ((4 : usize) *? col)) +? (3 : usize)))]_?;
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            (← ((4 : usize) *? col))
            (← ((← ((← ((← (gf_mul2 s0)) ^^^? (← (gf_mul3 s1)))) ^^^? s2))
              ^^^? s3)));
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            (← ((← ((4 : usize) *? col)) +? (1 : usize)))
            (← ((← ((← (s0 ^^^? (← (gf_mul2 s1)))) ^^^? (← (gf_mul3 s2))))
              ^^^? s3)));
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            (← ((← ((4 : usize) *? col)) +? (2 : usize)))
            (← ((← ((← (s0 ^^^? s1)) ^^^? (← (gf_mul2 s2))))
              ^^^? (← (gf_mul3 s3)))));
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            (← ((← ((4 : usize) *? col)) +? (3 : usize)))
            (← ((← ((← ((← (gf_mul3 s0)) ^^^? s1)) ^^^? s2))
              ^^^? (← (gf_mul2 s3)))));
        let col : usize ← (col +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk col result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  (pure result)

--  AES AddRoundKey: XOR state with round key.
def add_round_key (state : (RustArray u8 16)) (round_key : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (16 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← ((← state[i]_?) ^^^? (← round_key[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  (pure result)

--  Generic AES encryption core: applies num_rounds of AES transformation.
-- 
--  round_keys must have length num_rounds + 1.
--  Rounds 1..num_rounds-1 are full rounds (SubBytes, ShiftRows, MixColumns, AddRoundKey).
--  The final round omits MixColumns.
def aes_encrypt_rounds
    (plaintext : (RustArray u8 16))
    (round_keys : (RustSlice (RustArray u8 16)))
    (num_rounds : usize) :
    RustM (RustArray u8 16) := do
  let state : (RustArray u8 16) ←
    (add_round_key plaintext (← round_keys[(0 : usize)]_?));
  let round : usize := (1 : usize);
  let ⟨round, state⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨round, state⟩ => (do (pure true) : RustM Bool))
      (fun ⟨round, state⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt round num_rounds) : RustM Bool))
      (fun ⟨round, state⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk round state)
      (fun ⟨round, state⟩ =>
        (do
        let state : (RustArray u8 16) ← (sub_bytes state);
        let state : (RustArray u8 16) ← (shift_rows state);
        let state : (RustArray u8 16) ← (mix_columns state);
        let state : (RustArray u8 16) ←
          (add_round_key state (← round_keys[round]_?));
        let round : usize ← (round +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk round state)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  let state : (RustArray u8 16) ← (sub_bytes state);
  let state : (RustArray u8 16) ← (shift_rows state);
  let state : (RustArray u8 16) ←
    (add_round_key state (← round_keys[num_rounds]_?));
  (pure state)

--  AES-128 key expansion (FIPS 197, Section 5.2).
-- 
--  Expands a 16-byte key into 11 round keys (Nk=4, Nr=10).
def aes128_key_expand (key : (RustArray u8 16)) :
    RustM (RustArray (RustArray u8 16) 11) := do
  let round_keys : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (11 : usize));
  let round_keys : (RustArray (RustArray u8 16) 11) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      round_keys
      (0 : usize)
      key);
  let round : usize := (1 : usize);
  let ⟨round, round_keys⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨round, round_keys⟩ => (do (pure true) : RustM Bool))
      (fun ⟨round, round_keys⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.le round (10 : usize)) : RustM Bool))
      (fun ⟨round, round_keys⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk round round_keys)
      (fun ⟨round, round_keys⟩ =>
        (do
        let prev : (RustArray u8 16) ← round_keys[(← (round -? (1 : usize)))]_?;
        let rk : (RustArray u8 16) ←
          (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
        let rot : (RustArray u8 4) :=
          #v[(← prev[(13 : usize)]_?),
               (← prev[(14 : usize)]_?),
               (← prev[(15 : usize)]_?),
               (← prev[(12 : usize)]_?)];
        let j : usize := (0 : usize);
        let ⟨j, rk⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, rk⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, rk⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (4 : usize)) : RustM Bool))
            (fun ⟨j, rk⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j rk)
            (fun ⟨j, rk⟩ =>
              (do
              let sbox_out : u8 ←
                SBOX[(← (Rust_primitives.Hax.cast_op (← rot[j]_?)))]_?;
              let rk : (RustArray u8 16) ←
                if (← (Rust_primitives.Hax.Machine_int.eq j (0 : usize))) then
                  let rk : (RustArray u8 16) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      rk
                      j
                      (← ((← ((← prev[j]_?) ^^^? sbox_out))
                        ^^^? (← RCON[(← (round -? (1 : usize)))]_?))));
                  (pure rk)
                else
                  let rk : (RustArray u8 16) ←
                    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                      rk
                      j
                      (← ((← prev[j]_?) ^^^? sbox_out)));
                  (pure rk);
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j rk)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
        let j : usize := (4 : usize);
        let ⟨j, rk⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, rk⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, rk⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (16 : usize)) : RustM Bool))
            (fun ⟨j, rk⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j rk)
            (fun ⟨j, rk⟩ =>
              (do
              let rk : (RustArray u8 16) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  rk
                  j
                  (← ((← rk[(← (j -? (4 : usize)))]_?) ^^^? (← prev[j]_?))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j rk)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
        let round_keys : (RustArray (RustArray u8 16) 11) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            round_keys
            round
            rk);
        let round : usize ← (round +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk round round_keys)) :
        RustM
        (Rust_primitives.Hax.Tuple2 usize (RustArray (RustArray u8 16) 11)))));
  (pure round_keys)

--  AES-128 single-block encryption (FIPS 197).
-- 
--  Pure value-passing: takes key and plaintext, returns ciphertext.
--  10 rounds (9 full + final without MixColumns).
def aes128_encrypt (key : (RustArray u8 16)) (plaintext : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let round_keys : (RustArray (RustArray u8 16) 11) ← (aes128_key_expand key);
  (aes_encrypt_rounds
    plaintext
    (← (Rust_primitives.unsize round_keys))
    (10 : usize))

--  AES-256 key expansion (FIPS 197, Section 5.2).
-- 
--  Expands a 32-byte key into 15 round keys (Nk=8, Nr=14).
-- 
--  The AES-256 key schedule processes 8 columns (32 bytes) at a time:
--  - Every 8th column (i % 8 == 0): RotWord + SubWord + Rcon
--  - Every 4th column within a group (i % 8 == 4): SubWord only (no RotWord)
--  - All other columns: simple XOR with previous
def aes256_key_expand (key : (RustArray u8 32)) :
    RustM (RustArray (RustArray u8 16) 15) := do
  let w : (RustArray (RustArray u8 4) 60) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (4 : usize)))
      (60 : usize));
  let i : usize := (0 : usize);
  let ⟨i, w⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, w⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (8 : usize)) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i w)
      (fun ⟨i, w⟩ =>
        (do
        let w : (RustArray (RustArray u8 4) 60) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            i
            #v[(← key[(← ((4 : usize) *? i))]_?),
                 (← key[(← ((← ((4 : usize) *? i)) +? (1 : usize)))]_?),
                 (← key[(← ((← ((4 : usize) *? i)) +? (2 : usize)))]_?),
                 (← key[(← ((← ((4 : usize) *? i)) +? (3 : usize)))]_?)]);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i w)) :
        RustM
        (Rust_primitives.Hax.Tuple2 usize (RustArray (RustArray u8 4) 60)))));
  let i : usize := (8 : usize);
  let ⟨i, w⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, w⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (60 : usize)) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i w)
      (fun ⟨i, w⟩ =>
        (do
        let temp : (RustArray u8 4) ← w[(← (i -? (1 : usize)))]_?;
        let temp : (RustArray u8 4) ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← (i %? (8 : usize)))
            (0 : usize))) then
            let rotated : (RustArray u8 4) :=
              #v[(← temp[(1 : usize)]_?),
                   (← temp[(2 : usize)]_?),
                   (← temp[(3 : usize)]_?),
                   (← temp[(0 : usize)]_?)];
            let temp : (RustArray u8 4) :=
              #v[(← ((← SBOX[
                       (← (Rust_primitives.Hax.cast_op
                         (← rotated[(0 : usize)]_?)))
                       ]_?)
                     ^^^? (← RCON[
                       (← ((← (i /? (8 : usize))) -? (1 : usize)))
                       ]_?))),
                   (← SBOX[
                     (← (Rust_primitives.Hax.cast_op
                       (← rotated[(1 : usize)]_?)))
                     ]_?),
                   (← SBOX[
                     (← (Rust_primitives.Hax.cast_op
                       (← rotated[(2 : usize)]_?)))
                     ]_?),
                   (← SBOX[
                     (← (Rust_primitives.Hax.cast_op
                       (← rotated[(3 : usize)]_?)))
                     ]_?)];
            (pure temp)
          else
            if
            (← (Rust_primitives.Hax.Machine_int.eq
              (← (i %? (8 : usize)))
              (4 : usize))) then
              let temp : (RustArray u8 4) :=
                #v[(← SBOX[
                       (← (Rust_primitives.Hax.cast_op (← temp[(0 : usize)]_?)))
                       ]_?),
                     (← SBOX[
                       (← (Rust_primitives.Hax.cast_op (← temp[(1 : usize)]_?)))
                       ]_?),
                     (← SBOX[
                       (← (Rust_primitives.Hax.cast_op (← temp[(2 : usize)]_?)))
                       ]_?),
                     (← SBOX[
                       (← (Rust_primitives.Hax.cast_op (← temp[(3 : usize)]_?)))
                       ]_?)];
              (pure temp)
            else
              (pure temp);
        let j : usize := (0 : usize);
        let ⟨j, temp⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, temp⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, temp⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (4 : usize)) : RustM Bool))
            (fun ⟨j, temp⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j temp)
            (fun ⟨j, temp⟩ =>
              (do
              let temp : (RustArray u8 4) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  temp
                  j
                  (← ((← temp[j]_?)
                    ^^^? (← (← w[(← (i -? (8 : usize)))]_?)[j]_?))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j temp)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 4)))));
        let w : (RustArray (RustArray u8 4) 60) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            i
            temp);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i w)) :
        RustM
        (Rust_primitives.Hax.Tuple2 usize (RustArray (RustArray u8 4) 60)))));
  let round_keys : (RustArray (RustArray u8 16) 15) ←
    (Rust_primitives.Hax.repeat
      (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))
      (15 : usize));
  let r : usize := (0 : usize);
  let ⟨r, round_keys⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨r, round_keys⟩ => (do (pure true) : RustM Bool))
      (fun ⟨r, round_keys⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt r (15 : usize)) : RustM Bool))
      (fun ⟨r, round_keys⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk r round_keys)
      (fun ⟨r, round_keys⟩ =>
        (do
        let j : usize := (0 : usize);
        let ⟨j, round_keys⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, round_keys⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, round_keys⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (4 : usize)) : RustM Bool))
            (fun ⟨j, round_keys⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j round_keys)
            (fun ⟨j, round_keys⟩ =>
              (do
              let round_keys : (RustArray (RustArray u8 16) 15) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  round_keys
                  r
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← round_keys[r]_?)
                    (← ((4 : usize) *? j))
                    (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                      (0 : usize)
                      ]_?))));
              let round_keys : (RustArray (RustArray u8 16) 15) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  round_keys
                  r
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← round_keys[r]_?)
                    (← ((← ((4 : usize) *? j)) +? (1 : usize)))
                    (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                      (1 : usize)
                      ]_?))));
              let round_keys : (RustArray (RustArray u8 16) 15) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  round_keys
                  r
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← round_keys[r]_?)
                    (← ((← ((4 : usize) *? j)) +? (2 : usize)))
                    (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                      (2 : usize)
                      ]_?))));
              let round_keys : (RustArray (RustArray u8 16) 15) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  round_keys
                  r
                  (←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    (← round_keys[r]_?)
                    (← ((← ((4 : usize) *? j)) +? (3 : usize)))
                    (← (← w[(← ((← ((4 : usize) *? r)) +? j))]_?)[
                      (3 : usize)
                      ]_?))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j round_keys)) :
              RustM
              (Rust_primitives.Hax.Tuple2
                usize
                (RustArray (RustArray u8 16) 15)))));
        let r : usize ← (r +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk r round_keys)) :
        RustM
        (Rust_primitives.Hax.Tuple2 usize (RustArray (RustArray u8 16) 15)))));
  (pure round_keys)

--  AES-256 single-block encryption (FIPS 197).
-- 
--  Pure value-passing: takes 32-byte key and plaintext, returns ciphertext.
--  14 rounds (13 full + final without MixColumns).
def aes256_encrypt (key : (RustArray u8 32)) (plaintext : (RustArray u8 16)) :
    RustM (RustArray u8 16) := do
  let round_keys : (RustArray (RustArray u8 16) 15) ← (aes256_key_expand key);
  (aes_encrypt_rounds
    plaintext
    (← (Rust_primitives.unsize round_keys))
    (14 : usize))

end Libcrux_specs_hax.Aes


namespace Libcrux_specs_hax.Gf128

--  Reduction polynomial R = x^7 + x^2 + x + 1, placed at the MSB end.
--  This is 0xe1000000000000000000000000000000 as u128.
def R : u128 := RustM.of_isOk (do ((225 : u128) <<<? (120 : i32))) (by rfl)

--  Multiply two elements in GF(2^128) using the NIST GCM convention.
-- 
--  Schoolbook multiplication, MSB-first. The algorithm processes each bit
--  of b from the most significant to the least significant, accumulating
--  into z and reducing v after each step.
def gf128_mul (a : u128) (b : u128) : RustM u128 := do
  let z : u128 := (0 : u128);
  let v : u128 := a;
  let i : i32 := (0 : i32);
  let ⟨i, v, z⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, v, z⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, v, z⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (128 : i32)) : RustM Bool))
      (fun ⟨i, v, z⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk i v z)
      (fun ⟨i, v, z⟩ =>
        (do
        let z : u128 ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← (b >>>? (← ((127 : i32) -? i)))) &&&? (1 : u128)))
            (1 : u128))) then
            let z : u128 ← (z ^^^? v);
            (pure z)
          else
            (pure z);
        let carry : u128 ← (v &&&? (1 : u128));
        let v : u128 ← (v >>>? (1 : i32));
        let v : u128 ←
          if (← (Rust_primitives.Hax.Machine_int.eq carry (1 : u128))) then
            let v : u128 ← (v ^^^? R);
            (pure v)
          else
            (pure v);
        let i : i32 ← (i +? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple3.mk i v z)) :
        RustM (Rust_primitives.Hax.Tuple3 i32 u128 u128))));
  (pure z)

--  Convert a 16-byte big-endian array to u128.
def bytes_to_u128 (bytes : (RustSlice u8)) : RustM u128 := do
  let val : u128 := (0 : u128);
  let len : usize ←
    if
    (← (Rust_primitives.Hax.Machine_int.lt
      (← (Core_models.Slice.Impl.len u8 bytes))
      (16 : usize))) then
      (Core_models.Slice.Impl.len u8 bytes)
    else
      (pure (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, val⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, val⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, val⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i len) : RustM Bool))
      (fun ⟨i, val⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i val)
      (fun ⟨i, val⟩ =>
        (do
        let val : u128 ←
          (Rust_primitives.Hax.Machine_int.bitor
            val
            (← ((← (Rust_primitives.Hax.cast_op (← bytes[i]_?)))
              <<<? (← ((8 : usize) *? (← ((15 : usize) -? i)))))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i val)) :
        RustM (Rust_primitives.Hax.Tuple2 usize u128))));
  (pure val)

--  Convert a u128 to a 16-byte big-endian array.
def u128_to_bytes (val : u128) : RustM (RustArray u8 16) := do
  let bytes : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let i : usize := (0 : usize);
  let ⟨bytes, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨bytes, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨bytes, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (16 : usize)) : RustM Bool))
      (fun ⟨bytes, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk bytes i)
      (fun ⟨bytes, i⟩ =>
        (do
        let bytes : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            bytes
            i
            (← (Rust_primitives.Hax.cast_op
              (← (val >>>? (← ((8 : usize) *? (← ((15 : usize) -? i)))))))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk bytes i)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 16) usize))));
  (pure bytes)

--  GHASH: universal hash function used in GCM (NIST SP 800-38D, Section 6.4).
-- 
--  Processes data in 16-byte blocks, XORing each block into the accumulator
--  and multiplying by the hash subkey H. The last block is zero-padded if
--  its length is not a multiple of 16.
def ghash (h : u128) (data : (RustSlice u8)) : RustM u128 := do
  let acc : u128 := (0 : u128);
  let num_full_blocks : usize ←
    ((← (Core_models.Slice.Impl.len u8 data)) /? (16 : usize));
  let i : usize := (0 : usize);
  let ⟨acc, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, i⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt i num_full_blocks) : RustM Bool))
      (fun ⟨acc, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc i)
      (fun ⟨acc, i⟩ =>
        (do
        let block : u128 ←
          (bytes_to_u128
            (← data[
              (Core_models.Ops.Range.Range.mk
                (start := (← ((16 : usize) *? i)))
                (_end := (← ((← ((16 : usize) *? i)) +? (16 : usize)))))
              ]_?));
        let acc : u128 ← (gf128_mul (← (acc ^^^? block)) h);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc i)) :
        RustM (Rust_primitives.Hax.Tuple2 u128 usize))));
  let remainder : usize ←
    ((← (Core_models.Slice.Impl.len u8 data)) %? (16 : usize));
  let acc : u128 ←
    if (← (Rust_primitives.Hax.Machine_int.gt remainder (0 : usize))) then
      let padded : (RustArray u8 16) ←
        (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
      let offset : usize ← (num_full_blocks *? (16 : usize));
      let j : usize := (0 : usize);
      let ⟨j, padded⟩ ←
        (Rust_primitives.Hax.while_loop
          (fun ⟨j, padded⟩ => (do (pure true) : RustM Bool))
          (fun ⟨j, padded⟩ =>
            (do (Rust_primitives.Hax.Machine_int.lt j remainder) : RustM Bool))
          (fun ⟨j, padded⟩ =>
            (do
            (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
            RustM Hax_lib.Int.Int))
          (Rust_primitives.Hax.Tuple2.mk j padded)
          (fun ⟨j, padded⟩ =>
            (do
            let padded : (RustArray u8 16) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                padded
                j
                (← data[(← (offset +? j))]_?));
            let j : usize ← (j +? (1 : usize));
            (pure (Rust_primitives.Hax.Tuple2.mk j padded)) :
            RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
      let block : u128 ← (bytes_to_u128 (← (Rust_primitives.unsize padded)));
      let acc : u128 ← (gf128_mul (← (acc ^^^? block)) h);
      (pure acc)
    else
      (pure acc);
  (pure acc)

end Libcrux_specs_hax.Gf128


namespace Libcrux_specs_hax.Aes_gcm

--  Increment the rightmost 32 bits of a 16-byte counter block (big-endian).
def inc32 (counter : (RustArray u8 16)) : RustM (RustArray u8 16) := do
  let result : (RustArray u8 16) := counter;
  let ctr : u32 ←
    (Core_models.Num.Impl_8.from_be_bytes
      #v[(← result[(12 : usize)]_?),
           (← result[(13 : usize)]_?),
           (← result[(14 : usize)]_?),
           (← result[(15 : usize)]_?)]);
  let incremented : u32 ← (Core_models.Num.Impl_8.wrapping_add ctr (1 : u32));
  let bytes : (RustArray u8 4) ←
    (Core_models.Num.Impl_8.to_be_bytes incremented);
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (12 : usize)
      (← bytes[(0 : usize)]_?));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (13 : usize)
      (← bytes[(1 : usize)]_?));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (14 : usize)
      (← bytes[(2 : usize)]_?));
  let result : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (15 : usize)
      (← bytes[(3 : usize)]_?));
  (pure result)

--  XOR a keystream block with a data block, handling partial last blocks.
def xor_block (data : (RustSlice u8)) (keystream : (RustArray u8 16)) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let result : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let len : usize ← (Core_models.Slice.Impl.len u8 data);
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i len) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            result
            (← ((← data[i]_?) ^^^? (← keystream[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  (pure result)

--  Build the GHASH input: A || pad(A) || C || pad(C) || len(A) || len(C)
-- 
--  Where pad(X) pads X to a 16-byte boundary with zeros, and lengths are
--  in bits encoded as big-endian u64.
def build_ghash_input (aad : (RustSlice u8)) (ciphertext : (RustSlice u8)) :
    RustM (Alloc.Vec.Vec u8 Alloc.Alloc.Global) := do
  let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let i : usize := (0 : usize);
  let ⟨i, input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt
          i
          (← (Core_models.Slice.Impl.len u8 aad))) :
        RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i input)
      (fun ⟨i, input⟩ =>
        (do
        let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global input (← aad[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let aad_pad : usize ←
    ((← ((16 : usize)
        -? (← ((← (Core_models.Slice.Impl.len u8 aad)) %? (16 : usize)))))
      %? (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i aad_pad) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i input)
      (fun ⟨i, input⟩ =>
        (do
        let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global input (0 : u8));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let i : usize := (0 : usize);
  let ⟨i, input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt
          i
          (← (Core_models.Slice.Impl.len u8 ciphertext))) :
        RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i input)
      (fun ⟨i, input⟩ =>
        (do
        let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            input
            (← ciphertext[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let ct_pad : usize ←
    ((← ((16 : usize)
        -? (← ((← (Core_models.Slice.Impl.len u8 ciphertext))
          %? (16 : usize)))))
      %? (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i ct_pad) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i input)
      (fun ⟨i, input⟩ =>
        (do
        let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global input (0 : u8));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let aad_bits : u64 ←
    ((← (Rust_primitives.Hax.cast_op (← (Core_models.Slice.Impl.len u8 aad))))
      *? (8 : u64));
  let ct_bits : u64 ←
    ((← (Rust_primitives.Hax.cast_op
        (← (Core_models.Slice.Impl.len u8 ciphertext))))
      *? (8 : u64));
  let aad_len_bytes : (RustArray u8 8) ←
    (Core_models.Num.Impl_9.to_be_bytes aad_bits);
  let ct_len_bytes : (RustArray u8 8) ←
    (Core_models.Num.Impl_9.to_be_bytes ct_bits);
  let i : usize := (0 : usize);
  let ⟨i, input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (8 : usize)) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i input)
      (fun ⟨i, input⟩ =>
        (do
        let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            input
            (← aad_len_bytes[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let i : usize := (0 : usize);
  let ⟨i, input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (8 : usize)) : RustM Bool))
      (fun ⟨i, input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i input)
      (fun ⟨i, input⟩ =>
        (do
        let input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            input
            (← ct_len_bytes[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  (pure input)

--  Generic AES-GCM encryption using a caller-provided block cipher.
-- 
--  key_encrypt: function that encrypts a single 16-byte block under the key.
--  nonce: 12-byte nonce (IV).
--  aad: additional authenticated data (not encrypted, but authenticated).
--  plaintext: data to encrypt and authenticate.
-- 
--  Returns (ciphertext, tag).
def aes_gcm_encrypt_generic
    (impl_Fn([u8;_16])_-__[u8;_16] : Type)
    [trait_constr_aes_gcm_encrypt_generic_associated_type_i0 :
      Core_models.Ops.Function.Fn.AssociatedTypes
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))]
    [trait_constr_aes_gcm_encrypt_generic_i0 : Core_models.Ops.Function.Fn
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
      (associatedTypes := {
        show
          Core_models.Ops.Function.Fn.AssociatedTypes
          impl_Fn([u8;_16])_-__[u8;_16]
          (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
        by infer_instance
        with sorry})]
    (key_encrypt : impl_Fn([u8;_16])_-__[u8;_16])
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (plaintext : (RustSlice u8)) :
    RustM
    (Rust_primitives.Hax.Tuple2
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      (RustArray u8 16))
    := do
  let h_bytes : (RustArray u8 16) ←
    (Core_models.Ops.Function.Fn.call
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
      key_encrypt
      (Rust_primitives.Hax.Tuple1.mk
        (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))));
  let h : u128 ←
    (Libcrux_specs_hax.Gf128.bytes_to_u128
      (← (Rust_primitives.unsize h_bytes)));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, j0⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, j0⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, j0⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (12 : usize)) : RustM Bool))
      (fun ⟨i, j0⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i j0)
      (fun ⟨i, j0⟩ =>
        (do
        let j0 : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            j0
            i
            (← nonce[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i j0)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (12 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (13 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (14 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (15 : usize)
      (1 : u8));
  let ciphertext : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let num_blocks : usize ←
    ((← ((← (Core_models.Slice.Impl.len u8 plaintext)) +? (15 : usize)))
      /? (16 : usize));
  let counter : (RustArray u8 16) := j0;
  let i : usize := (0 : usize);
  let ⟨ciphertext, counter, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨ciphertext, counter, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨ciphertext, counter, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i num_blocks) : RustM Bool))
      (fun ⟨ciphertext, counter, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk ciphertext counter i)
      (fun ⟨ciphertext, counter, i⟩ =>
        (do
        let counter : (RustArray u8 16) ← (inc32 counter);
        let keystream : (RustArray u8 16) ←
          (Core_models.Ops.Function.Fn.call
            impl_Fn([u8;_16])_-__[u8;_16]
            (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
            key_encrypt
            (Rust_primitives.Hax.Tuple1.mk counter));
        let block_start : usize ← (i *? (16 : usize));
        let block_end : usize ←
          if
          (← (Rust_primitives.Hax.Machine_int.gt
            (← (block_start +? (16 : usize)))
            (← (Core_models.Slice.Impl.len u8 plaintext)))) then
            (Core_models.Slice.Impl.len u8 plaintext)
          else
            (block_start +? (16 : usize));
        let encrypted : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (xor_block
            (← plaintext[
              (Core_models.Ops.Range.Range.mk
                (start := block_start)
                (_end := block_end))
              ]_?)
            keystream);
        let j : usize := (0 : usize);
        let ⟨ciphertext, j⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨ciphertext, j⟩ => (do (pure true) : RustM Bool))
            (fun ⟨ciphertext, j⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt
                j
                (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global encrypted))) :
              RustM Bool))
            (fun ⟨ciphertext, j⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk ciphertext j)
            (fun ⟨ciphertext, j⟩ =>
              (do
              let ciphertext : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                  ciphertext
                  (← encrypted[j]_?));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk ciphertext j)) :
              RustM
              (Rust_primitives.Hax.Tuple2
                (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
                usize))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple3.mk ciphertext counter i)) :
        RustM
        (Rust_primitives.Hax.Tuple3
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
          (RustArray u8 16)
          usize))));
  let ghash_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (build_ghash_input
      aad
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ciphertext)));
  let s : u128 ←
    (Libcrux_specs_hax.Gf128.ghash
      h
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ghash_input)));
  let encrypted_j0 : (RustArray u8 16) ←
    (Core_models.Ops.Function.Fn.call
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
      key_encrypt
      (Rust_primitives.Hax.Tuple1.mk j0));
  let encrypted_j0_val : u128 ←
    (Libcrux_specs_hax.Gf128.bytes_to_u128
      (← (Rust_primitives.unsize encrypted_j0)));
  let tag_val : u128 ← (encrypted_j0_val ^^^? s);
  let tag : (RustArray u8 16) ← (Libcrux_specs_hax.Gf128.u128_to_bytes tag_val);
  (pure (Rust_primitives.Hax.Tuple2.mk ciphertext tag))

--  Generic AES-GCM decryption using a caller-provided block cipher.
-- 
--  Returns Some(plaintext) if the tag is valid, None otherwise.
def aes_gcm_decrypt_generic
    (impl_Fn([u8;_16])_-__[u8;_16] : Type)
    [trait_constr_aes_gcm_decrypt_generic_associated_type_i0 :
      Core_models.Ops.Function.Fn.AssociatedTypes
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))]
    [trait_constr_aes_gcm_decrypt_generic_i0 : Core_models.Ops.Function.Fn
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
      (associatedTypes := {
        show
          Core_models.Ops.Function.Fn.AssociatedTypes
          impl_Fn([u8;_16])_-__[u8;_16]
          (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
        by infer_instance
        with sorry})]
    (key_encrypt : impl_Fn([u8;_16])_-__[u8;_16])
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (ciphertext : (RustSlice u8))
    (tag : (RustArray u8 16)) :
    RustM
    (Core_models.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    := do
  let h_bytes : (RustArray u8 16) ←
    (Core_models.Ops.Function.Fn.call
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
      key_encrypt
      (Rust_primitives.Hax.Tuple1.mk
        (← (Rust_primitives.Hax.repeat (0 : u8) (16 : usize)))));
  let h : u128 ←
    (Libcrux_specs_hax.Gf128.bytes_to_u128
      (← (Rust_primitives.unsize h_bytes)));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.repeat (0 : u8) (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, j0⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, j0⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, j0⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (12 : usize)) : RustM Bool))
      (fun ⟨i, j0⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i j0)
      (fun ⟨i, j0⟩ =>
        (do
        let j0 : (RustArray u8 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            j0
            i
            (← nonce[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i j0)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 16)))));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (12 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (13 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (14 : usize)
      (0 : u8));
  let j0 : (RustArray u8 16) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      j0
      (15 : usize)
      (1 : u8));
  let ghash_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (build_ghash_input aad ciphertext);
  let s : u128 ←
    (Libcrux_specs_hax.Gf128.ghash
      h
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ghash_input)));
  let encrypted_j0 : (RustArray u8 16) ←
    (Core_models.Ops.Function.Fn.call
      impl_Fn([u8;_16])_-__[u8;_16]
      (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
      key_encrypt
      (Rust_primitives.Hax.Tuple1.mk j0));
  let encrypted_j0_val : u128 ←
    (Libcrux_specs_hax.Gf128.bytes_to_u128
      (← (Rust_primitives.unsize encrypted_j0)));
  let expected_tag_val : u128 ← (encrypted_j0_val ^^^? s);
  let expected_tag : (RustArray u8 16) ←
    (Libcrux_specs_hax.Gf128.u128_to_bytes expected_tag_val);
  let tag_ok : Bool := true;
  let i : usize := (0 : usize);
  let ⟨i, tag_ok⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, tag_ok⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, tag_ok⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (16 : usize)) : RustM Bool))
      (fun ⟨i, tag_ok⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i tag_ok)
      (fun ⟨i, tag_ok⟩ =>
        (do
        let tag_ok : Bool ←
          if
          (← (Rust_primitives.Hax.Machine_int.ne
            (← tag[i]_?)
            (← expected_tag[i]_?))) then
            let tag_ok : Bool := false;
            (pure tag_ok)
          else
            (pure tag_ok);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i tag_ok)) :
        RustM (Rust_primitives.Hax.Tuple2 usize Bool))));
  if (← (Core_models.Ops.Bit.Not.not tag_ok)) then
    (pure Core_models.Option.Option.None)
  else
    let plaintext : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
      (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
    let num_blocks : usize ←
      ((← ((← (Core_models.Slice.Impl.len u8 ciphertext)) +? (15 : usize)))
        /? (16 : usize));
    let counter : (RustArray u8 16) := j0;
    let i : usize := (0 : usize);
    let ⟨counter, i, plaintext⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨counter, i, plaintext⟩ => (do (pure true) : RustM Bool))
        (fun ⟨counter, i, plaintext⟩ =>
          (do (Rust_primitives.Hax.Machine_int.lt i num_blocks) : RustM Bool))
        (fun ⟨counter, i, plaintext⟩ =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple3.mk counter i plaintext)
        (fun ⟨counter, i, plaintext⟩ =>
          (do
          let counter : (RustArray u8 16) ← (inc32 counter);
          let keystream : (RustArray u8 16) ←
            (Core_models.Ops.Function.Fn.call
              impl_Fn([u8;_16])_-__[u8;_16]
              (Rust_primitives.Hax.Tuple1 (RustArray u8 16))
              key_encrypt
              (Rust_primitives.Hax.Tuple1.mk counter));
          let block_start : usize ← (i *? (16 : usize));
          let block_end : usize ←
            if
            (← (Rust_primitives.Hax.Machine_int.gt
              (← (block_start +? (16 : usize)))
              (← (Core_models.Slice.Impl.len u8 ciphertext)))) then
              (Core_models.Slice.Impl.len u8 ciphertext)
            else
              (block_start +? (16 : usize));
          let decrypted : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
            (xor_block
              (← ciphertext[
                (Core_models.Ops.Range.Range.mk
                  (start := block_start)
                  (_end := block_end))
                ]_?)
              keystream);
          let j : usize := (0 : usize);
          let ⟨j, plaintext⟩ ←
            (Rust_primitives.Hax.while_loop
              (fun ⟨j, plaintext⟩ => (do (pure true) : RustM Bool))
              (fun ⟨j, plaintext⟩ =>
                (do
                (Rust_primitives.Hax.Machine_int.lt
                  j
                  (← (Alloc.Vec.Impl_1.len u8 Alloc.Alloc.Global decrypted))) :
                RustM Bool))
              (fun ⟨j, plaintext⟩ =>
                (do
                (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                RustM Hax_lib.Int.Int))
              (Rust_primitives.Hax.Tuple2.mk j plaintext)
              (fun ⟨j, plaintext⟩ =>
                (do
                let plaintext : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                  (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                    plaintext
                    (← decrypted[j]_?));
                let j : usize ← (j +? (1 : usize));
                (pure (Rust_primitives.Hax.Tuple2.mk j plaintext)) :
                RustM
                (Rust_primitives.Hax.Tuple2
                  usize
                  (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
          let i : usize ← (i +? (1 : usize));
          (pure (Rust_primitives.Hax.Tuple3.mk counter i plaintext)) :
          RustM
          (Rust_primitives.Hax.Tuple3
            (RustArray u8 16)
            usize
            (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
    (pure (Core_models.Option.Option.Some plaintext))

--  AES-128-GCM authenticated encryption (NIST SP 800-38D).
-- 
--  Returns (ciphertext, 16-byte authentication tag).
def aes128_gcm_encrypt
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (plaintext : (RustSlice u8)) :
    RustM
    (Rust_primitives.Hax.Tuple2
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      (RustArray u8 16))
    := do
  let k : (RustArray u8 16) := key;
  (aes_gcm_encrypt_generic ((RustArray u8 16) -> RustM (RustArray u8 16))
    (fun block =>
      (do
      (Libcrux_specs_hax.Aes.aes128_encrypt k block) : RustM (RustArray u8 16)))
    nonce
    aad
    plaintext)

--  AES-128-GCM authenticated decryption (NIST SP 800-38D).
-- 
--  Returns Some(plaintext) if the tag verifies, None otherwise.
def aes128_gcm_decrypt
    (key : (RustArray u8 16))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (ciphertext : (RustSlice u8))
    (tag : (RustArray u8 16)) :
    RustM
    (Core_models.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    := do
  let k : (RustArray u8 16) := key;
  (aes_gcm_decrypt_generic ((RustArray u8 16) -> RustM (RustArray u8 16))
    (fun block =>
      (do
      (Libcrux_specs_hax.Aes.aes128_encrypt k block) : RustM (RustArray u8 16)))
    nonce
    aad
    ciphertext
    tag)

--  AES-256-GCM authenticated encryption (NIST SP 800-38D).
-- 
--  Returns (ciphertext, 16-byte authentication tag).
def aes256_gcm_encrypt
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (plaintext : (RustSlice u8)) :
    RustM
    (Rust_primitives.Hax.Tuple2
      (Alloc.Vec.Vec u8 Alloc.Alloc.Global)
      (RustArray u8 16))
    := do
  let k : (RustArray u8 32) := key;
  (aes_gcm_encrypt_generic ((RustArray u8 16) -> RustM (RustArray u8 16))
    (fun block =>
      (do
      (Libcrux_specs_hax.Aes.aes256_encrypt k block) : RustM (RustArray u8 16)))
    nonce
    aad
    plaintext)

--  AES-256-GCM authenticated decryption (NIST SP 800-38D).
-- 
--  Returns Some(plaintext) if the tag verifies, None otherwise.
def aes256_gcm_decrypt
    (key : (RustArray u8 32))
    (nonce : (RustArray u8 12))
    (aad : (RustSlice u8))
    (ciphertext : (RustSlice u8))
    (tag : (RustArray u8 16)) :
    RustM
    (Core_models.Option.Option (Alloc.Vec.Vec u8 Alloc.Alloc.Global))
    := do
  let k : (RustArray u8 32) := key;
  (aes_gcm_decrypt_generic ((RustArray u8 16) -> RustM (RustArray u8 16))
    (fun block =>
      (do
      (Libcrux_specs_hax.Aes.aes256_encrypt k block) : RustM (RustArray u8 16)))
    nonce
    aad
    ciphertext
    tag)

end Libcrux_specs_hax.Aes_gcm


namespace Libcrux_specs_hax.Curve25519

--  Bitmask for 51-bit limbs.
def MASK51 : u64 :=
  RustM.of_isOk (do ((← ((1 : u64) <<<? (51 : i32))) -? (1 : u64))) (by rfl)

--  a24 = 121665 (the constant (A-2)/4 for curve25519, where A = 486662).
--  See RFC 7748, Section 5.
def A24 : u64 := (121665 : u64)

--  The zero field element.
def fe_zero (_ : Rust_primitives.Hax.Tuple0) : RustM (RustArray u64 5) := do
  (pure #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64), (0 : u64)])

--  The one field element.
def fe_one (_ : Rust_primitives.Hax.Tuple0) : RustM (RustArray u64 5) := do
  (pure #v[(1 : u64), (0 : u64), (0 : u64), (0 : u64), (0 : u64)])

--  Propagate carries across limbs, reducing mod p = 2^255 - 19.
--  After this, each limb is at most 51 bits.
def fe_carry (a : (RustArray u64 5)) : RustM (RustArray u64 5) := do
  let r : (RustArray u64 5) := a;
  let carry : u64 ← ((← r[(0 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (0 : usize)
      (← ((← r[(0 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (1 : usize)
      (← ((← r[(1 : usize)]_?) +? carry)));
  let carry : u64 ← ((← r[(1 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (1 : usize)
      (← ((← r[(1 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (2 : usize)
      (← ((← r[(2 : usize)]_?) +? carry)));
  let carry : u64 ← ((← r[(2 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (2 : usize)
      (← ((← r[(2 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (3 : usize)
      (← ((← r[(3 : usize)]_?) +? carry)));
  let carry : u64 ← ((← r[(3 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (3 : usize)
      (← ((← r[(3 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (4 : usize)
      (← ((← r[(4 : usize)]_?) +? carry)));
  let carry : u64 ← ((← r[(4 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (4 : usize)
      (← ((← r[(4 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (0 : usize)
      (← ((← r[(0 : usize)]_?) +? (← (carry *? (19 : u64))))));
  let carry : u64 ← ((← r[(0 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (0 : usize)
      (← ((← r[(0 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (1 : usize)
      (← ((← r[(1 : usize)]_?) +? carry)));
  (pure r)

--  Field addition with carry propagation.
def fe_add (a : (RustArray u64 5)) (b : (RustArray u64 5)) :
    RustM (RustArray u64 5) := do
  (fe_carry
    #v[(← ((← a[(0 : usize)]_?) +? (← b[(0 : usize)]_?))),
         (← ((← a[(1 : usize)]_?) +? (← b[(1 : usize)]_?))),
         (← ((← a[(2 : usize)]_?) +? (← b[(2 : usize)]_?))),
         (← ((← a[(3 : usize)]_?) +? (← b[(3 : usize)]_?))),
         (← ((← a[(4 : usize)]_?) +? (← b[(4 : usize)]_?)))])

--  Field subtraction with carry propagation.
-- 
--  We add 2*p as a bias before subtracting to keep values positive.
--  2*p = 2*(2^255 - 19) in 51-bit limbs =
--    [2*(2^51-19), 2*(2^51-1), 2*(2^51-1), 2*(2^51-1), 2*(2^51-1)]
--  = [2^52 - 38,   2^52 - 2,   2^52 - 2,   2^52 - 2,   2^52 - 2]
def fe_sub (a : (RustArray u64 5)) (b : (RustArray u64 5)) :
    RustM (RustArray u64 5) := do
  (fe_carry
    #v[(← ((← ((← a[(0 : usize)]_?) +? (4503599627370458 : u64)))
           -? (← b[(0 : usize)]_?))),
         (← ((← ((← a[(1 : usize)]_?) +? (4503599627370494 : u64)))
           -? (← b[(1 : usize)]_?))),
         (← ((← ((← a[(2 : usize)]_?) +? (4503599627370494 : u64)))
           -? (← b[(2 : usize)]_?))),
         (← ((← ((← a[(3 : usize)]_?) +? (4503599627370494 : u64)))
           -? (← b[(3 : usize)]_?))),
         (← ((← ((← a[(4 : usize)]_?) +? (4503599627370494 : u64)))
           -? (← b[(4 : usize)]_?)))])

--  Field multiplication using schoolbook with u128 intermediates.
-- 
--  Reduction uses 2^255 = 19 (mod p): when a product lands in limb >= 5,
--  it wraps to limb (i-5) with a factor of 19.
def fe_mul (a : (RustArray u64 5)) (b : (RustArray u64 5)) :
    RustM (RustArray u64 5) := do
  let b1_19 : u128 ←
    ((19 : u128) *? (← (Rust_primitives.Hax.cast_op (← b[(1 : usize)]_?))));
  let b2_19 : u128 ←
    ((19 : u128) *? (← (Rust_primitives.Hax.cast_op (← b[(2 : usize)]_?))));
  let b3_19 : u128 ←
    ((19 : u128) *? (← (Rust_primitives.Hax.cast_op (← b[(3 : usize)]_?))));
  let b4_19 : u128 ←
    ((19 : u128) *? (← (Rust_primitives.Hax.cast_op (← b[(4 : usize)]_?))));
  let a0 : u128 ← (Rust_primitives.Hax.cast_op (← a[(0 : usize)]_?));
  let a1 : u128 ← (Rust_primitives.Hax.cast_op (← a[(1 : usize)]_?));
  let a2 : u128 ← (Rust_primitives.Hax.cast_op (← a[(2 : usize)]_?));
  let a3 : u128 ← (Rust_primitives.Hax.cast_op (← a[(3 : usize)]_?));
  let a4 : u128 ← (Rust_primitives.Hax.cast_op (← a[(4 : usize)]_?));
  let b0 : u128 ← (Rust_primitives.Hax.cast_op (← b[(0 : usize)]_?));
  let b1 : u128 ← (Rust_primitives.Hax.cast_op (← b[(1 : usize)]_?));
  let b2 : u128 ← (Rust_primitives.Hax.cast_op (← b[(2 : usize)]_?));
  let b3 : u128 ← (Rust_primitives.Hax.cast_op (← b[(3 : usize)]_?));
  let b4 : u128 ← (Rust_primitives.Hax.cast_op (← b[(4 : usize)]_?));
  let r0 : u128 ←
    ((← ((← ((← ((← (a0 *? b0)) +? (← (a1 *? b4_19)))) +? (← (a2 *? b3_19))))
        +? (← (a3 *? b2_19))))
      +? (← (a4 *? b1_19)));
  let r1 : u128 ←
    ((← ((← ((← ((← (a0 *? b1)) +? (← (a1 *? b0)))) +? (← (a2 *? b4_19))))
        +? (← (a3 *? b3_19))))
      +? (← (a4 *? b2_19)));
  let r2 : u128 ←
    ((← ((← ((← ((← (a0 *? b2)) +? (← (a1 *? b1)))) +? (← (a2 *? b0))))
        +? (← (a3 *? b4_19))))
      +? (← (a4 *? b3_19)));
  let r3 : u128 ←
    ((← ((← ((← ((← (a0 *? b3)) +? (← (a1 *? b2)))) +? (← (a2 *? b1))))
        +? (← (a3 *? b0))))
      +? (← (a4 *? b4_19)));
  let r4 : u128 ←
    ((← ((← ((← ((← (a0 *? b4)) +? (← (a1 *? b3)))) +? (← (a2 *? b2))))
        +? (← (a3 *? b1))))
      +? (← (a4 *? b0)));
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      (← ((← (Rust_primitives.Hax.cast_op r0)) &&&? MASK51)));
  let carry : u128 ← (r0 >>>? (51 : i32));
  let s1 : u128 ← (r1 +? carry);
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (1 : usize)
      (← ((← (Rust_primitives.Hax.cast_op s1)) &&&? MASK51)));
  let carry : u128 ← (s1 >>>? (51 : i32));
  let s2 : u128 ← (r2 +? carry);
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (2 : usize)
      (← ((← (Rust_primitives.Hax.cast_op s2)) &&&? MASK51)));
  let carry : u128 ← (s2 >>>? (51 : i32));
  let s3 : u128 ← (r3 +? carry);
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (3 : usize)
      (← ((← (Rust_primitives.Hax.cast_op s3)) &&&? MASK51)));
  let carry : u128 ← (s3 >>>? (51 : i32));
  let s4 : u128 ← (r4 +? carry);
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (4 : usize)
      (← ((← (Rust_primitives.Hax.cast_op s4)) &&&? MASK51)));
  let carry : u128 ← (s4 >>>? (51 : i32));
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      (← ((← out[(0 : usize)]_?)
        +? (← ((← (Rust_primitives.Hax.cast_op carry)) *? (19 : u64))))));
  let c : u64 ← ((← out[(0 : usize)]_?) >>>? (51 : i32));
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (0 : usize)
      (← ((← out[(0 : usize)]_?) &&&? MASK51)));
  let out : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      out
      (1 : usize)
      (← ((← out[(1 : usize)]_?) +? c)));
  (pure out)

--  Field squaring.
def fe_sq (a : (RustArray u64 5)) : RustM (RustArray u64 5) := do (fe_mul a a)

--  Compute a^(2^n) by repeated squaring.
def fe_sq_n (a : (RustArray u64 5)) (n : u32) : RustM (RustArray u64 5) := do
  let r : (RustArray u64 5) := a;
  let i : u32 := (0 : u32);
  let ⟨i, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, r⟩ => (do (Rust_primitives.Hax.Machine_int.lt i n) : RustM Bool))
      (fun ⟨i, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i r)
      (fun ⟨i, r⟩ =>
        (do
        let r : (RustArray u64 5) ← (fe_sq r);
        let i : u32 ← (i +? (1 : u32));
        (pure (Rust_primitives.Hax.Tuple2.mk i r)) :
        RustM (Rust_primitives.Hax.Tuple2 u32 (RustArray u64 5)))));
  (pure r)

--  Field inversion: a^(p-2) mod p, using the standard addition chain
--  for the exponent 2^255 - 21.
def fe_inv (a : (RustArray u64 5)) : RustM (RustArray u64 5) := do
  let z2 : (RustArray u64 5) ← (fe_sq a);
  let t : (RustArray u64 5) ← (fe_sq (← (fe_sq z2)));
  let z9 : (RustArray u64 5) ← (fe_mul a t);
  let z11 : (RustArray u64 5) ← (fe_mul z2 z9);
  let t : (RustArray u64 5) ← (fe_sq z11);
  let z_5_0 : (RustArray u64 5) ← (fe_mul z9 t);
  let z_10_0 : (RustArray u64 5) ← (fe_mul (← (fe_sq_n z_5_0 (5 : u32))) z_5_0);
  let z_20_0 : (RustArray u64 5) ←
    (fe_mul (← (fe_sq_n z_10_0 (10 : u32))) z_10_0);
  let z_40_0 : (RustArray u64 5) ←
    (fe_mul (← (fe_sq_n z_20_0 (20 : u32))) z_20_0);
  let z_50_0 : (RustArray u64 5) ←
    (fe_mul (← (fe_sq_n z_40_0 (10 : u32))) z_10_0);
  let z_100_0 : (RustArray u64 5) ←
    (fe_mul (← (fe_sq_n z_50_0 (50 : u32))) z_50_0);
  let z_200_0 : (RustArray u64 5) ←
    (fe_mul (← (fe_sq_n z_100_0 (100 : u32))) z_100_0);
  let z_250_0 : (RustArray u64 5) ←
    (fe_mul (← (fe_sq_n z_200_0 (50 : u32))) z_50_0);
  let z_255_5 : (RustArray u64 5) ← (fe_sq_n z_250_0 (5 : u32));
  (fe_mul z_255_5 z11)

--  Canonical reduction mod p = 2^255 - 19.
def fe_reduce (a : (RustArray u64 5)) : RustM (RustArray u64 5) := do
  let r : (RustArray u64 5) ← (fe_carry a);
  let r : (RustArray u64 5) ← (fe_carry r);
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (0 : usize)
      (← ((← r[(0 : usize)]_?) +? (19 : u64))));
  let c0 : u64 ← ((← s[(0 : usize)]_?) >>>? (51 : i32));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (0 : usize)
      (← ((← s[(0 : usize)]_?) &&&? MASK51)));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (1 : usize)
      (← ((← r[(1 : usize)]_?) +? c0)));
  let c1 : u64 ← ((← s[(1 : usize)]_?) >>>? (51 : i32));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (1 : usize)
      (← ((← s[(1 : usize)]_?) &&&? MASK51)));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (2 : usize)
      (← ((← r[(2 : usize)]_?) +? c1)));
  let c2 : u64 ← ((← s[(2 : usize)]_?) >>>? (51 : i32));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (2 : usize)
      (← ((← s[(2 : usize)]_?) &&&? MASK51)));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (3 : usize)
      (← ((← r[(3 : usize)]_?) +? c2)));
  let c3 : u64 ← ((← s[(3 : usize)]_?) >>>? (51 : i32));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (3 : usize)
      (← ((← s[(3 : usize)]_?) &&&? MASK51)));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (4 : usize)
      (← ((← r[(4 : usize)]_?) +? c3)));
  let c4 : u64 ← ((← s[(4 : usize)]_?) >>>? (51 : i32));
  let s : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      s
      (4 : usize)
      (← ((← s[(4 : usize)]_?) &&&? MASK51)));
  let mask : u64 ← (Core_models.Num.Impl_9.wrapping_neg c4);
  (pure #v[(← (Rust_primitives.Hax.Machine_int.bitor
               (← ((← s[(0 : usize)]_?) &&&? mask))
               (← ((← r[(0 : usize)]_?)
                 &&&? (← (Rust_primitives.Hax.Machine_int.not mask)))))),
             (← (Rust_primitives.Hax.Machine_int.bitor
               (← ((← s[(1 : usize)]_?) &&&? mask))
               (← ((← r[(1 : usize)]_?)
                 &&&? (← (Rust_primitives.Hax.Machine_int.not mask)))))),
             (← (Rust_primitives.Hax.Machine_int.bitor
               (← ((← s[(2 : usize)]_?) &&&? mask))
               (← ((← r[(2 : usize)]_?)
                 &&&? (← (Rust_primitives.Hax.Machine_int.not mask)))))),
             (← (Rust_primitives.Hax.Machine_int.bitor
               (← ((← s[(3 : usize)]_?) &&&? mask))
               (← ((← r[(3 : usize)]_?)
                 &&&? (← (Rust_primitives.Hax.Machine_int.not mask)))))),
             (← (Rust_primitives.Hax.Machine_int.bitor
               (← ((← s[(4 : usize)]_?) &&&? mask))
               (← ((← r[(4 : usize)]_?)
                 &&&? (← (Rust_primitives.Hax.Machine_int.not mask))))))])

--  Deserialise 32 bytes (little-endian) into a field element.
--  Clears bit 255 per RFC 7748.
def fe_from_bytes (b : (RustArray u8 32)) : RustM (RustArray u64 5) := do
  let raw : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨i, raw⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, raw⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, raw⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, raw⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i raw)
      (fun ⟨i, raw⟩ =>
        (do
        let raw : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            raw
            i
            (← b[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i raw)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  let raw : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      raw
      (31 : usize)
      (← ((← raw[(31 : usize)]_?) &&&? (127 : u8))));
  let load8 : ((RustSlice u8) -> usize -> RustM u64) :=
    (fun buf off =>
      (do
      let v : u64 := (0 : u64);
      let j : usize := (0 : usize);
      let ⟨j, v⟩ ←
        (Rust_primitives.Hax.while_loop
          (fun ⟨j, v⟩ => (do (pure true) : RustM Bool))
          (fun ⟨j, v⟩ =>
            (do
            ((← (Rust_primitives.Hax.Machine_int.lt j (8 : usize)))
              &&? (← (Rust_primitives.Hax.Machine_int.lt
                (← (off +? j))
                (← (Core_models.Slice.Impl.len u8 buf))))) :
            RustM Bool))
          (fun ⟨j, v⟩ =>
            (do
            (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
            RustM Hax_lib.Int.Int))
          (Rust_primitives.Hax.Tuple2.mk j v)
          (fun ⟨j, v⟩ =>
            (do
            let v : u64 ←
              (Rust_primitives.Hax.Machine_int.bitor
                v
                (← ((← (Rust_primitives.Hax.cast_op (← buf[(← (off +? j))]_?)))
                  <<<? (← ((8 : usize) *? j)))));
            let j : usize ← (j +? (1 : usize));
            (pure (Rust_primitives.Hax.Tuple2.mk j v)) :
            RustM (Rust_primitives.Hax.Tuple2 usize u64))));
      (pure v) :
      RustM u64));
  (pure #v[(← ((← (Core_models.Ops.Function.Fn.call
                 ((RustSlice u8) -> usize -> RustM u64)
                 (Rust_primitives.Hax.Tuple2 (RustSlice u8) usize)
                 load8
                 (Rust_primitives.Hax.Tuple2.mk
                   (← (Rust_primitives.unsize raw))
                   (0 : usize))))
               &&&? MASK51)),
             (← ((← ((← (Core_models.Ops.Function.Fn.call
                   ((RustSlice u8) -> usize -> RustM u64)
                   (Rust_primitives.Hax.Tuple2 (RustSlice u8) usize)
                   load8
                   (Rust_primitives.Hax.Tuple2.mk
                     (← (Rust_primitives.unsize raw))
                     (6 : usize))))
                 >>>? (3 : i32)))
               &&&? MASK51)),
             (← ((← ((← (Core_models.Ops.Function.Fn.call
                   ((RustSlice u8) -> usize -> RustM u64)
                   (Rust_primitives.Hax.Tuple2 (RustSlice u8) usize)
                   load8
                   (Rust_primitives.Hax.Tuple2.mk
                     (← (Rust_primitives.unsize raw))
                     (12 : usize))))
                 >>>? (6 : i32)))
               &&&? MASK51)),
             (← ((← ((← (Core_models.Ops.Function.Fn.call
                   ((RustSlice u8) -> usize -> RustM u64)
                   (Rust_primitives.Hax.Tuple2 (RustSlice u8) usize)
                   load8
                   (Rust_primitives.Hax.Tuple2.mk
                     (← (Rust_primitives.unsize raw))
                     (19 : usize))))
                 >>>? (1 : i32)))
               &&&? MASK51)),
             (← ((← ((← (Core_models.Ops.Function.Fn.call
                   ((RustSlice u8) -> usize -> RustM u64)
                   (Rust_primitives.Hax.Tuple2 (RustSlice u8) usize)
                   load8
                   (Rust_primitives.Hax.Tuple2.mk
                     (← (Rust_primitives.unsize raw))
                     (24 : usize))))
                 >>>? (12 : i32)))
               &&&? MASK51))])

--  Serialise a field element to 32 bytes (little-endian).
def fe_to_bytes (a : (RustArray u64 5)) : RustM (RustArray u8 32) := do
  let r : (RustArray u64 5) ← (fe_reduce a);
  let words : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let words : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      words
      (0 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← r[(0 : usize)]_?)
        (← ((← r[(1 : usize)]_?) <<<? (51 : i32))))));
  let words : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      words
      (1 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← ((← r[(1 : usize)]_?) >>>? (13 : i32)))
        (← ((← r[(2 : usize)]_?) <<<? (38 : i32))))));
  let words : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      words
      (2 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← ((← r[(2 : usize)]_?) >>>? (26 : i32)))
        (← ((← r[(3 : usize)]_?) <<<? (25 : i32))))));
  let words : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      words
      (3 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← ((← r[(3 : usize)]_?) >>>? (39 : i32)))
        (← ((← r[(4 : usize)]_?) <<<? (12 : i32))))));
  let val : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let k : usize := (0 : usize);
  let ⟨k, val⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨k, val⟩ => (do (pure true) : RustM Bool))
      (fun ⟨k, val⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨k, val⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk k val)
      (fun ⟨k, val⟩ =>
        (do
        let b : (RustArray u8 8) ←
          (Core_models.Num.Impl_9.to_le_bytes (← words[k]_?));
        let j : usize := (0 : usize);
        let ⟨j, val⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, val⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, val⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, val⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j val)
            (fun ⟨j, val⟩ =>
              (do
              let val : (RustArray u8 32) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  val
                  (← ((← (k *? (8 : usize))) +? j))
                  (← b[j]_?));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j val)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk k val)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  (pure val)

--  Constant-time conditional swap. If swap == 1, exchange a and b.
def cswap (swap : u64) (a : (RustArray u64 5)) (b : (RustArray u64 5)) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 5) (RustArray u64 5)) := do
  let mask : u64 ← (Core_models.Num.Impl_9.wrapping_neg swap);
  let ra : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let rb : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let i : usize := (0 : usize);
  let ⟨i, ra, rb⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, ra, rb⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, ra, rb⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (5 : usize)) : RustM Bool))
      (fun ⟨i, ra, rb⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk i ra rb)
      (fun ⟨i, ra, rb⟩ =>
        (do
        let diff : u64 ← (mask &&&? (← ((← a[i]_?) ^^^? (← b[i]_?))));
        let ra : (RustArray u64 5) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            ra
            i
            (← ((← a[i]_?) ^^^? diff)));
        let rb : (RustArray u64 5) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            rb
            i
            (← ((← b[i]_?) ^^^? diff)));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple3.mk i ra rb)) :
        RustM
        (Rust_primitives.Hax.Tuple3
          usize
          (RustArray u64 5)
          (RustArray u64 5)))));
  (pure (Rust_primitives.Hax.Tuple2.mk ra rb))

--  Multiply a field element by the small constant 121666.
def fe_mul_121666 (a : (RustArray u64 5)) : RustM (RustArray u64 5) := do
  let c : u128 ← (Rust_primitives.Hax.cast_op A24);
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let t : u128 ← ((← (Rust_primitives.Hax.cast_op (← a[(0 : usize)]_?))) *? c);
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (0 : usize)
      (← ((← (Rust_primitives.Hax.cast_op t)) &&&? MASK51)));
  let carry : u128 ← (t >>>? (51 : i32));
  let t : u128 ←
    ((← ((← (Rust_primitives.Hax.cast_op (← a[(1 : usize)]_?))) *? c))
      +? carry);
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (1 : usize)
      (← ((← (Rust_primitives.Hax.cast_op t)) &&&? MASK51)));
  let carry : u128 ← (t >>>? (51 : i32));
  let t : u128 ←
    ((← ((← (Rust_primitives.Hax.cast_op (← a[(2 : usize)]_?))) *? c))
      +? carry);
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (2 : usize)
      (← ((← (Rust_primitives.Hax.cast_op t)) &&&? MASK51)));
  let carry : u128 ← (t >>>? (51 : i32));
  let t : u128 ←
    ((← ((← (Rust_primitives.Hax.cast_op (← a[(3 : usize)]_?))) *? c))
      +? carry);
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (3 : usize)
      (← ((← (Rust_primitives.Hax.cast_op t)) &&&? MASK51)));
  let carry : u128 ← (t >>>? (51 : i32));
  let t : u128 ←
    ((← ((← (Rust_primitives.Hax.cast_op (← a[(4 : usize)]_?))) *? c))
      +? carry);
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (4 : usize)
      (← ((← (Rust_primitives.Hax.cast_op t)) &&&? MASK51)));
  let carry : u128 ← (t >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (0 : usize)
      (← ((← r[(0 : usize)]_?)
        +? (← ((← (Rust_primitives.Hax.cast_op carry)) *? (19 : u64))))));
  let c2 : u64 ← ((← r[(0 : usize)]_?) >>>? (51 : i32));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (0 : usize)
      (← ((← r[(0 : usize)]_?) &&&? MASK51)));
  let r : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      r
      (1 : usize)
      (← ((← r[(1 : usize)]_?) +? c2)));
  (pure r)

--  X25519 scalar multiplication (RFC 7748).
-- 
--  Clamps the scalar, then performs a Montgomery ladder.
def x25519_scalarmult (k : (RustArray u8 32)) (u : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  let scalar : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨i, scalar⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, scalar⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, scalar⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, scalar⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i scalar)
      (fun ⟨i, scalar⟩ =>
        (do
        let scalar : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            scalar
            i
            (← k[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i scalar)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  let scalar : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      scalar
      (0 : usize)
      (← ((← scalar[(0 : usize)]_?) &&&? (248 : u8))));
  let scalar : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      scalar
      (31 : usize)
      (← ((← scalar[(31 : usize)]_?) &&&? (127 : u8))));
  let scalar : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      scalar
      (31 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← scalar[(31 : usize)]_?)
        (64 : u8))));
  let x_1 : (RustArray u64 5) ← (fe_from_bytes u);
  let x_2 : (RustArray u64 5) ← (fe_one Rust_primitives.Hax.Tuple0.mk);
  let z_2 : (RustArray u64 5) ← (fe_zero Rust_primitives.Hax.Tuple0.mk);
  let x_3 : (RustArray u64 5) := x_1;
  let z_3 : (RustArray u64 5) ← (fe_one Rust_primitives.Hax.Tuple0.mk);
  let swap : u64 := (0 : u64);
  let pos : i32 := (254 : i32);
  let ⟨pos, swap, x_2, x_3, z_2, z_3⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨pos, swap, x_2, x_3, z_2, z_3⟩ => (do (pure true) : RustM Bool))
      (fun ⟨pos, swap, x_2, x_3, z_2, z_3⟩ =>
        (do (Rust_primitives.Hax.Machine_int.ge pos (0 : i32)) : RustM Bool))
      (fun ⟨pos, swap, x_2, x_3, z_2, z_3⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple6.mk pos swap x_2 x_3 z_2 z_3)
      (fun ⟨pos, swap, x_2, x_3, z_2, z_3⟩ =>
        (do
        let byte_idx : usize ←
          (Rust_primitives.Hax.cast_op (← (pos >>>? (3 : i32))));
        let bit_idx : u32 ←
          (Rust_primitives.Hax.cast_op (← (pos &&&? (7 : i32))));
        let k_t : u64 ←
          (Rust_primitives.Hax.cast_op
            (← ((← ((← scalar[byte_idx]_?) >>>? bit_idx)) &&&? (1 : u8))));
        let swap : u64 ← (swap ^^^? k_t);
        let ⟨a, b⟩ ← (cswap swap x_2 x_3);
        let x_2 : (RustArray u64 5) := a;
        let x_3 : (RustArray u64 5) := b;
        let ⟨a, b⟩ ← (cswap swap z_2 z_3);
        let z_2 : (RustArray u64 5) := a;
        let z_3 : (RustArray u64 5) := b;
        let swap : u64 := k_t;
        let aa : (RustArray u64 5) ← (fe_add x_2 z_2);
        let bb : (RustArray u64 5) ← (fe_sub x_2 z_2);
        let aa_sq : (RustArray u64 5) ← (fe_sq aa);
        let bb_sq : (RustArray u64 5) ← (fe_sq bb);
        let e : (RustArray u64 5) ← (fe_sub aa_sq bb_sq);
        let cc : (RustArray u64 5) ← (fe_add x_3 z_3);
        let dd : (RustArray u64 5) ← (fe_sub x_3 z_3);
        let da : (RustArray u64 5) ← (fe_mul dd aa);
        let cb : (RustArray u64 5) ← (fe_mul cc bb);
        let x_3 : (RustArray u64 5) ← (fe_sq (← (fe_add da cb)));
        let z_3 : (RustArray u64 5) ←
          (fe_mul x_1 (← (fe_sq (← (fe_sub da cb)))));
        let x_2 : (RustArray u64 5) ← (fe_mul aa_sq bb_sq);
        let z_2 : (RustArray u64 5) ←
          (fe_mul e (← (fe_add aa_sq (← (fe_mul_121666 e)))));
        let pos : i32 ← (pos -? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple6.mk pos swap x_2 x_3 z_2 z_3)) :
        RustM
        (Rust_primitives.Hax.Tuple6
          i32
          u64
          (RustArray u64 5)
          (RustArray u64 5)
          (RustArray u64 5)
          (RustArray u64 5)))));
  let ⟨a, _⟩ ← (cswap swap x_2 x_3);
  let x_2 : (RustArray u64 5) := a;
  let ⟨a, _⟩ ← (cswap swap z_2 z_3);
  let z_2 : (RustArray u64 5) := a;
  let result : (RustArray u64 5) ← (fe_mul x_2 (← (fe_inv z_2)));
  (fe_to_bytes result)

--  X25519 with the standard base point u = 9.
def x25519_base (k : (RustArray u8 32)) : RustM (RustArray u8 32) := do
  let base : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let base : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      base
      (0 : usize)
      (9 : u8));
  (x25519_scalarmult k base)

end Libcrux_specs_hax.Curve25519


namespace Libcrux_specs_hax.X25519

--  X25519 scalar multiplication: compute scalar * point on Curve25519.
def scalarmult (scalar : (RustArray u8 32)) (point : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  (Libcrux_specs_hax.Curve25519.x25519_scalarmult scalar point)

--  X25519 base point multiplication: compute scalar * 9.
def base_mult (scalar : (RustArray u8 32)) : RustM (RustArray u8 32) := do
  (Libcrux_specs_hax.Curve25519.x25519_base scalar)

end Libcrux_specs_hax.X25519


namespace Libcrux_specs_hax.P256

--  The P-256 field element type: [u64; 4], big-endian limb order.
abbrev P256FieldElement : Type := (RustArray u64 4)

--  A point on the P-256 curve in Jacobian coordinates.
--  The point at infinity is represented by Z = 0.
structure P256Point where
  x : (RustArray u64 4)
  y : (RustArray u64 4)
  z : (RustArray u64 4)

@[instance] opaque Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes P256Point :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  Core_models.Clone.Clone P256Point :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes P256Point :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Marker.Copy P256Point :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Fmt.Debug.AssociatedTypes P256Point :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Fmt.Debug P256Point :=
  by constructor <;> exact Inhabited.default

--  Prime p = 2^256 - 2^224 + 2^192 + 2^96 - 1
--          = 0xFFFFFFFF00000001000000000000000000000000FFFFFFFFFFFFFFFFFFFFFFFF
def P256_P : (RustArray u64 4) :=
  RustM.of_isOk
    (do
    #v[(18446744069414584321 : u64),
         (0 : u64),
         (4294967295 : u64),
         (18446744073709551615 : u64)])
    (by rfl)

--  Curve parameter b.
--  b = 0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B
def P256_B : (RustArray u64 4) :=
  RustM.of_isOk
    (do
    #v[(6540974713487397863 : u64),
         (12964664127075681980 : u64),
         (7285987128567378166 : u64),
         (4309448131093880907 : u64)])
    (by rfl)

--  Group order n.
--  n = 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
def P256_N : (RustArray u64 4) :=
  RustM.of_isOk
    (do
    #v[(18446744069414584320 : u64),
         (18446744073709551615 : u64),
         (13611842547513532036 : u64),
         (17562291160714782033 : u64)])
    (by rfl)

--  Base point x-coordinate (Gx).
--  Gx = 0x6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296
def P256_GX : (RustArray u64 4) :=
  RustM.of_isOk
    (do
    #v[(7716867327612699207 : u64),
         (17923454489921339634 : u64),
         (8575836109218198432 : u64),
         (17627433388654248598 : u64)])
    (by rfl)

--  Base point y-coordinate (Gy).
--  Gy = 0x4FE342E2FE1A7F9B8EE7EB4A7C0F9E162BCE33576B315ECECBB6406837BF51F5
def P256_GY : (RustArray u64 4) :=
  RustM.of_isOk
    (do
    #v[(5756518291402817435 : u64),
         (10297457778147434006 : u64),
         (3156516839386865358 : u64),
         (14678990851816772085 : u64)])
    (by rfl)

--  Compare two 256-bit numbers (big-endian limb order).
--  Returns -1 if a < b, 0 if a == b, 1 if a > b.
def cmp256 (a : (RustArray u64 4)) (b : (RustArray u64 4)) : RustM i32 := do
  let i : usize := (0 : usize);
  match
    (← (Rust_primitives.Hax.while_loop_return
      (fun i => (do (pure true) : RustM Bool))
      (fun i =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun i =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      i
      (fun i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.lt (← a[i]_?) (← b[i]_?))) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Core_models.Ops.Control_flow.ControlFlow.Break (-1 : i32))))
        else
          if (← (Rust_primitives.Hax.Machine_int.gt (← a[i]_?) (← b[i]_?))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Core_models.Ops.Control_flow.ControlFlow.Break (1 : i32))))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (← (i +? (1 : usize))))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Core_models.Ops.Control_flow.ControlFlow
            i32
            (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 usize))
          usize)))))
  with
    | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
    | (Core_models.Ops.Control_flow.ControlFlow.Continue  i) => (pure (0 : i32))

--  256-bit addition: a + b, returns (result, carry).
def add256 (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 4) u64) := do
  let r : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let carry : u128 := (0 : u128);
  let i : usize := (4 : usize);
  let ⟨carry, i, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨carry, i, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨carry, i, r⟩ =>
        (do (Rust_primitives.Hax.Machine_int.gt i (0 : usize)) : RustM Bool))
      (fun ⟨carry, i, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk carry i r)
      (fun ⟨carry, i, r⟩ =>
        (do
        let i : usize ← (i -? (1 : usize));
        let s : u128 ←
          ((← ((← (Rust_primitives.Hax.cast_op (← a[i]_?)))
              +? (← (Rust_primitives.Hax.cast_op (← b[i]_?)))))
            +? carry);
        let r : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            r
            i
            (← (Rust_primitives.Hax.cast_op s)));
        let carry : u128 ← (s >>>? (64 : i32));
        (pure (Rust_primitives.Hax.Tuple3.mk carry i r)) :
        RustM (Rust_primitives.Hax.Tuple3 u128 usize (RustArray u64 4)))));
  (pure (Rust_primitives.Hax.Tuple2.mk
    r
    (← (Rust_primitives.Hax.cast_op carry))))

--  256-bit subtraction: a - b, returns (result, borrow).
--  borrow is 1 if a < b.
def sub256 (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 4) u64) := do
  let r : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let borrow : u128 := (0 : u128);
  let i : usize := (4 : usize);
  let ⟨borrow, i, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨borrow, i, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨borrow, i, r⟩ =>
        (do (Rust_primitives.Hax.Machine_int.gt i (0 : usize)) : RustM Bool))
      (fun ⟨borrow, i, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk borrow i r)
      (fun ⟨borrow, i, r⟩ =>
        (do
        let i : usize ← (i -? (1 : usize));
        let s : u128 ←
          (Core_models.Num.Impl_10.wrapping_sub
            (← (Core_models.Num.Impl_10.wrapping_sub
              (← (Rust_primitives.Hax.cast_op (← a[i]_?)))
              (← (Rust_primitives.Hax.cast_op (← b[i]_?)))))
            borrow);
        let r : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            r
            i
            (← (Rust_primitives.Hax.cast_op s)));
        let borrow : u128 ← ((← (s >>>? (127 : i32))) &&&? (1 : u128));
        (pure (Rust_primitives.Hax.Tuple3.mk borrow i r)) :
        RustM (Rust_primitives.Hax.Tuple3 u128 usize (RustArray u64 4)))));
  (pure (Rust_primitives.Hax.Tuple2.mk
    r
    (← (Rust_primitives.Hax.cast_op borrow))))

--  Field addition: (a + b) mod p.
def fp_add (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (RustArray u64 4) := do
  let ⟨r, carry⟩ ← (add256 a b);
  let r : (RustArray u64 4) ←
    if
    (← ((← (Rust_primitives.Hax.Machine_int.eq carry (1 : u64)))
      ||? (← (Rust_primitives.Hax.Machine_int.ge
        (← (cmp256 r P256_P))
        (0 : i32))))) then
      let ⟨s, _⟩ ← (sub256 r P256_P);
      let r : (RustArray u64 4) := s;
      (pure r)
    else
      (pure r);
  (pure r)

--  Field subtraction: (a - b) mod p.
def fp_sub (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (RustArray u64 4) := do
  let ⟨r, borrow⟩ ← (sub256 a b);
  if (← (Rust_primitives.Hax.Machine_int.eq borrow (1 : u64))) then
    let ⟨s, _⟩ ← (add256 r P256_P);
    (pure s)
  else
    (pure r)

--  Field negation: (-a) mod p.
def fp_neg (a : (RustArray u64 4)) : RustM (RustArray u64 4) := do
  if
  (← (Core_models.Cmp.PartialEq.eq
    (RustArray u64 4)
    (RustArray u64 4) a #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)])) then
    (pure a)
  else
    (fp_sub #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)] a)

--  256x256 -> 512-bit multiplication (schoolbook).
--  Result stored as [u64; 8] in big-endian order.
def mul256_full (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (RustArray u64 8) := do
  let r : (RustArray u64 9) ←
    (Rust_primitives.Hax.repeat (0 : u64) (9 : usize));
  let i : usize := (0 : usize);
  let ⟨i, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, r⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun ⟨i, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i r)
      (fun ⟨i, r⟩ =>
        (do
        let carry : u128 := (0 : u128);
        let j : usize := (0 : usize);
        let ⟨carry, j, r⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨carry, j, r⟩ => (do (pure true) : RustM Bool))
            (fun ⟨carry, j, r⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (4 : usize)) : RustM Bool))
            (fun ⟨carry, j, r⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple3.mk carry j r)
            (fun ⟨carry, j, r⟩ =>
              (do
              let prod : u128 ←
                ((← ((← ((← (Rust_primitives.Hax.cast_op
                        (← a[(← ((3 : usize) -? i))]_?)))
                      *? (← (Rust_primitives.Hax.cast_op
                        (← b[(← ((3 : usize) -? j))]_?)))))
                    +? (← (Rust_primitives.Hax.cast_op (← r[(← (i +? j))]_?)))))
                  +? carry);
              let r : (RustArray u64 9) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  r
                  (← (i +? j))
                  (← (Rust_primitives.Hax.cast_op prod)));
              let carry : u128 ← (prod >>>? (64 : i32));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple3.mk carry j r)) :
              RustM
              (Rust_primitives.Hax.Tuple3 u128 usize (RustArray u64 9)))));
        let r : (RustArray u64 9) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            r
            (← (i +? (4 : usize)))
            (← (Rust_primitives.Hax.cast_op carry)));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i r)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 9)))));
  let out : (RustArray u64 8) ←
    (Rust_primitives.Hax.repeat (0 : u64) (8 : usize));
  let k : usize := (0 : usize);
  let ⟨k, out⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨k, out⟩ => (do (pure true) : RustM Bool))
      (fun ⟨k, out⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (8 : usize)) : RustM Bool))
      (fun ⟨k, out⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk k out)
      (fun ⟨k, out⟩ =>
        (do
        let out : (RustArray u64 8) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            out
            (← ((7 : usize) -? k))
            (← r[k]_?));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk k out)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 8)))));
  (pure out)

--  Reduce a 512-bit number mod p using the NIST P-256 fast reduction.
-- 
--  The 512-bit input c is split into 32-bit words c[0]..c[15] (big-endian).
--  Then the result is:
--    T + S1 + S2 + S3 + S4 - D1 - D2 - D3 - D4  (mod p)
-- 
--  See NIST SP 800-186 / Solinas reduction for P-256.
def reduce_mod_p (c : (RustArray u64 8)) : RustM (RustArray u64 4) := do
  let w : (RustArray u32 16) ←
    (Rust_primitives.Hax.repeat (0 : u32) (16 : usize));
  let i : usize := (0 : usize);
  let ⟨i, w⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, w⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (8 : usize)) : RustM Bool))
      (fun ⟨i, w⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i w)
      (fun ⟨i, w⟩ =>
        (do
        let w : (RustArray u32 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            (← ((2 : usize) *? i))
            (← (Rust_primitives.Hax.cast_op (← ((← c[i]_?) >>>? (32 : i32))))));
        let w : (RustArray u32 16) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            w
            (← ((← ((2 : usize) *? i)) +? (1 : usize)))
            (← (Rust_primitives.Hax.cast_op (← c[i]_?))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i w)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u32 16)))));
  let
    build : (u32 ->
    u32 ->
    u32 ->
    u32 ->
    u32 ->
    u32 ->
    u32 ->
    u32 ->
    RustM (RustArray u64 4)) :=
    (fun a7 a6 a5 a4 a3 a2 a1 a0 =>
      (do
      (pure #v[(← (Rust_primitives.Hax.Machine_int.bitor
                   (← ((← (Rust_primitives.Hax.cast_op a7)) <<<? (32 : i32)))
                   (← (Rust_primitives.Hax.cast_op a6)))),
                 (← (Rust_primitives.Hax.Machine_int.bitor
                   (← ((← (Rust_primitives.Hax.cast_op a5)) <<<? (32 : i32)))
                   (← (Rust_primitives.Hax.cast_op a4)))),
                 (← (Rust_primitives.Hax.Machine_int.bitor
                   (← ((← (Rust_primitives.Hax.cast_op a3)) <<<? (32 : i32)))
                   (← (Rust_primitives.Hax.cast_op a2)))),
                 (← (Rust_primitives.Hax.Machine_int.bitor
                   (← ((← (Rust_primitives.Hax.cast_op a1)) <<<? (32 : i32)))
                   (← (Rust_primitives.Hax.cast_op a0))))]) :
      RustM (RustArray u64 4)));
  let c : (usize -> RustM u32) :=
    (fun idx => (do w[(← ((15 : usize) -? idx))]_? : RustM u32));
  let t : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (7 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (6 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (5 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (4 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (3 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (2 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (1 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (0 : usize))))));
  let s1 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (12 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (11 : usize))))
        (0 : u32)
        (0 : u32)
        (0 : u32)));
  let s2 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (12 : usize))))
        (0 : u32)
        (0 : u32)
        (0 : u32)));
  let s3 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))
        (0 : u32)
        (0 : u32)
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (10 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (9 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (8 : usize))))));
  let s4 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (8 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (11 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (10 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (9 : usize))))));
  let d1 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (10 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (8 : usize))))
        (0 : u32)
        (0 : u32)
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (12 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (11 : usize))))));
  let d2 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (11 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (9 : usize))))
        (0 : u32)
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (12 : usize))))));
  let d3 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (12 : usize))))
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (10 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (9 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (8 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))));
  let d4 : (RustArray u64 4) ←
    (Core_models.Ops.Function.Fn.call
      (u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      u32 ->
      RustM (RustArray u64 4))
      (Rust_primitives.Hax.Tuple8 u32 u32 u32 u32 u32 u32 u32 u32)
      build
      (Rust_primitives.Hax.Tuple8.mk
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (13 : usize))))
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (11 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (10 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (9 : usize))))
        (0 : u32)
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (15 : usize))))
        (← (Core_models.Ops.Function.Fn.call
          (usize -> RustM u32)
          (Rust_primitives.Hax.Tuple1 usize)
          c
          (Rust_primitives.Hax.Tuple1.mk (14 : usize))))));
  let acc : (RustArray i128 4) ←
    (Rust_primitives.Hax.repeat (0 : i128) (4 : usize));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?) +? (← (Rust_primitives.Hax.cast_op (← t[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              +? (← ((2 : i128)
                *? (← (Rust_primitives.Hax.cast_op (← s1[k]_?))))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              +? (← ((2 : i128)
                *? (← (Rust_primitives.Hax.cast_op (← s2[k]_?))))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              +? (← (Rust_primitives.Hax.cast_op (← s3[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              +? (← (Rust_primitives.Hax.cast_op (← s4[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              -? (← (Rust_primitives.Hax.cast_op (← d1[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              -? (← (Rust_primitives.Hax.cast_op (← d2[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              -? (← (Rust_primitives.Hax.cast_op (← d3[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let k : usize := (0 : usize);
  let ⟨acc, k⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, k⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt k (4 : usize)) : RustM Bool))
      (fun ⟨acc, k⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc k)
      (fun ⟨acc, k⟩ =>
        (do
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            k
            (← ((← acc[k]_?)
              -? (← (Rust_primitives.Hax.cast_op (← d4[k]_?))))));
        let k : usize ← (k +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk acc k)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray i128 4) usize))));
  let carry : i128 := (0 : i128);
  let j : usize := (4 : usize);
  let ⟨acc, carry, j⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, carry, j⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, carry, j⟩ =>
        (do (Rust_primitives.Hax.Machine_int.gt j (0 : usize)) : RustM Bool))
      (fun ⟨acc, carry, j⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk acc carry j)
      (fun ⟨acc, carry, j⟩ =>
        (do
        let j : usize ← (j -? (1 : usize));
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            j
            (← ((← acc[j]_?) +? carry)));
        let carry : i128 ← ((← acc[j]_?) >>>? (64 : i32));
        let acc : (RustArray i128 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            j
            (← ((← acc[j]_?) &&&? (18446744073709551615 : i128))));
        (pure (Rust_primitives.Hax.Tuple3.mk acc carry j)) :
        RustM (Rust_primitives.Hax.Tuple3 (RustArray i128 4) i128 usize))));
  let r : (RustArray u64 4) :=
    #v[(← (Rust_primitives.Hax.cast_op (← acc[(0 : usize)]_?))),
         (← (Rust_primitives.Hax.cast_op (← acc[(1 : usize)]_?))),
         (← (Rust_primitives.Hax.cast_op (← acc[(2 : usize)]_?))),
         (← (Rust_primitives.Hax.cast_op (← acc[(3 : usize)]_?)))];
  let ⟨carry, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨carry, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨carry, r⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt carry (0 : i128)) : RustM Bool))
      (fun ⟨carry, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk carry r)
      (fun ⟨carry, r⟩ =>
        (do
        let ⟨s, _⟩ ← (add256 r P256_P);
        let r : (RustArray u64 4) := s;
        let carry : i128 ← (carry +? (1 : i128));
        (pure (Rust_primitives.Hax.Tuple2.mk carry r)) :
        RustM (Rust_primitives.Hax.Tuple2 i128 (RustArray u64 4)))));
  let ⟨carry, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨carry, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨carry, r⟩ =>
        (do (Rust_primitives.Hax.Machine_int.gt carry (0 : i128)) : RustM Bool))
      (fun ⟨carry, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk carry r)
      (fun ⟨carry, r⟩ =>
        (do
        let ⟨s, _⟩ ← (sub256 r P256_P);
        let r : (RustArray u64 4) := s;
        let carry : i128 ← (carry -? (1 : i128));
        (pure (Rust_primitives.Hax.Tuple2.mk carry r)) :
        RustM (Rust_primitives.Hax.Tuple2 i128 (RustArray u64 4)))));
  let r : (RustArray u64 4) ←
    (Rust_primitives.Hax.while_loop
      (fun r => (do (pure true) : RustM Bool))
      (fun r =>
        (do
        (Rust_primitives.Hax.Machine_int.ge (← (cmp256 r P256_P)) (0 : i32)) :
        RustM Bool))
      (fun r =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      r
      (fun r =>
        (do
        let ⟨s, _⟩ ← (sub256 r P256_P);
        let r : (RustArray u64 4) := s;
        (pure r) :
        RustM (RustArray u64 4))));
  (pure r)

--  Field multiplication: (a * b) mod p.
def fp_mul (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (RustArray u64 4) := do
  let wide : (RustArray u64 8) ← (mul256_full a b);
  (reduce_mod_p wide)

--  Field squaring: a^2 mod p.
def fp_sq (a : (RustArray u64 4)) : RustM (RustArray u64 4) := do (fp_mul a a)

--  Field inversion via Fermat's little theorem: a^(p-2) mod p.
def fp_inv (a : (RustArray u64 4)) : RustM (RustArray u64 4) := do
  let result : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let result : (RustArray u64 4) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      result
      (3 : usize)
      (1 : u64));
  let exp : (RustArray u64 4) :=
    #v[(18446744069414584321 : u64),
         (0 : u64),
         (4294967295 : u64),
         (18446744073709551613 : u64)];
  let bit_pos : i32 := (255 : i32);
  let ⟨bit_pos, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨bit_pos, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨bit_pos, result⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.ge bit_pos (0 : i32)) : RustM Bool))
      (fun ⟨bit_pos, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk bit_pos result)
      (fun ⟨bit_pos, result⟩ =>
        (do
        let result : (RustArray u64 4) ← (fp_sq result);
        let word : usize ←
          (Rust_primitives.Hax.cast_op (← (bit_pos /? (64 : i32))));
        let bit : u32 ←
          (Rust_primitives.Hax.cast_op (← (bit_pos %? (64 : i32))));
        let result : (RustArray u64 4) ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← ((← exp[(← ((3 : usize) -? word))]_?) >>>? bit))
              &&&? (1 : u64)))
            (1 : u64))) then
            let result : (RustArray u64 4) ← (fp_mul result a);
            (pure result)
          else
            (pure result);
        let bit_pos : i32 ← (bit_pos -? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk bit_pos result)) :
        RustM (Rust_primitives.Hax.Tuple2 i32 (RustArray u64 4)))));
  (pure result)

--  Encode a field element to 32 bytes (big-endian).
def fp_to_bytes (a : (RustArray u64 4)) : RustM (RustArray u8 32) := do
  let out : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨i, out⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, out⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, out⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun ⟨i, out⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i out)
      (fun ⟨i, out⟩ =>
        (do
        let bytes : (RustArray u8 8) ←
          (Core_models.Num.Impl_9.to_be_bytes (← a[i]_?));
        let j : usize := (0 : usize);
        let ⟨j, out⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, out⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, out⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, out⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j out)
            (fun ⟨j, out⟩ =>
              (do
              let out : (RustArray u8 32) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  out
                  (← ((← (i *? (8 : usize))) +? j))
                  (← bytes[j]_?));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j out)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i out)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  (pure out)

--  Decode a field element from 32 bytes (big-endian).
def fp_from_bytes (b : (RustArray u8 32)) : RustM (RustArray u64 4) := do
  let r : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let i : usize := (0 : usize);
  let ⟨i, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, r⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun ⟨i, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i r)
      (fun ⟨i, r⟩ =>
        (do
        let word : u64 := (0 : u64);
        let j : usize := (0 : usize);
        let ⟨j, word⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, word⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, word⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, word⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j word)
            (fun ⟨j, word⟩ =>
              (do
              let word : u64 ←
                (Rust_primitives.Hax.Machine_int.bitor
                  (← (word <<<? (8 : i32)))
                  (← (Rust_primitives.Hax.cast_op
                    (← b[(← ((← (i *? (8 : usize))) +? j))]_?))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j word)) :
              RustM (Rust_primitives.Hax.Tuple2 usize u64))));
        let r : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            r
            i
            word);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i r)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 4)))));
  (pure r)

--  Compare two 256-bit numbers for the scalar field.
def cmp256_n (a : (RustArray u64 4)) (b : (RustArray u64 4)) : RustM i32 := do
  (cmp256 a b)

--  Scalar addition: (a + b) mod n.
def fn_add (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (RustArray u64 4) := do
  let ⟨r, carry⟩ ← (add256 a b);
  let r : (RustArray u64 4) ←
    if
    (← ((← (Rust_primitives.Hax.Machine_int.eq carry (1 : u64)))
      ||? (← (Rust_primitives.Hax.Machine_int.ge
        (← (cmp256_n r P256_N))
        (0 : i32))))) then
      let ⟨s, _⟩ ← (sub256 r P256_N);
      let r : (RustArray u64 4) := s;
      (pure r)
    else
      (pure r);
  (pure r)

--  Reduce a 512-bit number mod n by trial subtraction.
--  This is a spec-quality implementation — not optimised.
def reduce_mod_n (c : (RustArray u64 8)) : RustM (RustArray u64 4) := do
  let acc : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let bit_pos : i32 := (511 : i32);
  let ⟨acc, bit_pos⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, bit_pos⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, bit_pos⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.ge bit_pos (0 : i32)) : RustM Bool))
      (fun ⟨acc, bit_pos⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc bit_pos)
      (fun ⟨acc, bit_pos⟩ =>
        (do
        let carry_bit : u64 := (0 : u64);
        let k : usize := (4 : usize);
        let ⟨acc, carry_bit, k⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨acc, carry_bit, k⟩ => (do (pure true) : RustM Bool))
            (fun ⟨acc, carry_bit, k⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.gt k (0 : usize)) : RustM Bool))
            (fun ⟨acc, carry_bit, k⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple3.mk acc carry_bit k)
            (fun ⟨acc, carry_bit, k⟩ =>
              (do
              let k : usize ← (k -? (1 : usize));
              let new_carry : u64 ← ((← acc[k]_?) >>>? (63 : i32));
              let acc : (RustArray u64 4) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  acc
                  k
                  (← (Rust_primitives.Hax.Machine_int.bitor
                    (← ((← acc[k]_?) <<<? (1 : i32)))
                    carry_bit)));
              let carry_bit : u64 := new_carry;
              (pure (Rust_primitives.Hax.Tuple3.mk acc carry_bit k)) :
              RustM (Rust_primitives.Hax.Tuple3 (RustArray u64 4) u64 usize))));
        let word_idx : usize ←
          (Rust_primitives.Hax.cast_op (← (bit_pos /? (64 : i32))));
        let bit_idx : u32 ←
          (Rust_primitives.Hax.cast_op (← (bit_pos %? (64 : i32))));
        let bit_val : u64 ←
          ((← ((← c[(← ((7 : usize) -? word_idx))]_?) >>>? bit_idx))
            &&&? (1 : u64));
        let ⟨s, c1⟩ ← (add256 acc #v[(0 : u64), (0 : u64), (0 : u64), bit_val]);
        let acc : (RustArray u64 4) := s;
        let total_carry : u64 ← (carry_bit +? c1);
        let acc : (RustArray u64 4) ←
          if
          (← ((← (Rust_primitives.Hax.Machine_int.gt total_carry (0 : u64)))
            ||? (← (Rust_primitives.Hax.Machine_int.ge
              (← (cmp256 acc P256_N))
              (0 : i32))))) then
            let ⟨s, _⟩ ← (sub256 acc P256_N);
            let acc : (RustArray u64 4) := s;
            (pure acc)
          else
            (pure acc);
        let bit_pos : i32 ← (bit_pos -? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk acc bit_pos)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 4) i32))));
  (pure acc)

--  Scalar multiplication: (a * b) mod n.
def fn_mul (a : (RustArray u64 4)) (b : (RustArray u64 4)) :
    RustM (RustArray u64 4) := do
  let wide : (RustArray u64 8) ← (mul256_full a b);
  (reduce_mod_n wide)

--  Scalar inversion: a^(n-2) mod n via Fermat's little theorem.
def fn_inv (a : (RustArray u64 4)) : RustM (RustArray u64 4) := do
  let exp : (RustArray u64 4) :=
    #v[(18446744069414584320 : u64),
         (18446744073709551615 : u64),
         (13611842547513532036 : u64),
         (17562291160714782031 : u64)];
  let result : (RustArray u64 4) :=
    #v[(0 : u64), (0 : u64), (0 : u64), (1 : u64)];
  let bit_pos : i32 := (255 : i32);
  let ⟨bit_pos, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨bit_pos, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨bit_pos, result⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.ge bit_pos (0 : i32)) : RustM Bool))
      (fun ⟨bit_pos, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk bit_pos result)
      (fun ⟨bit_pos, result⟩ =>
        (do
        let result : (RustArray u64 4) ← (fn_mul result result);
        let word : usize ←
          (Rust_primitives.Hax.cast_op (← (bit_pos /? (64 : i32))));
        let bit : u32 ←
          (Rust_primitives.Hax.cast_op (← (bit_pos %? (64 : i32))));
        let result : (RustArray u64 4) ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← ((← exp[(← ((3 : usize) -? word))]_?) >>>? bit))
              &&&? (1 : u64)))
            (1 : u64))) then
            let result : (RustArray u64 4) ← (fn_mul result a);
            (pure result)
          else
            (pure result);
        let bit_pos : i32 ← (bit_pos -? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk bit_pos result)) :
        RustM (Rust_primitives.Hax.Tuple2 i32 (RustArray u64 4)))));
  (pure result)

--  Decode a 32-byte big-endian integer as a scalar mod n.
def fn_from_bytes (b : (RustArray u8 32)) : RustM (RustArray u64 4) := do
  let v : (RustArray u64 4) ← (fp_from_bytes b);
  if
  (← (Rust_primitives.Hax.Machine_int.ge (← (cmp256 v P256_N)) (0 : i32))) then
    let ⟨s, _⟩ ← (sub256 v P256_N);
    (pure s)
  else
    (pure v)

--  The point at infinity (identity element).
def point_identity (_ : Rust_primitives.Hax.Tuple0) : RustM P256Point := do
  (pure (P256Point.mk
    (x := #v[(0 : u64), (0 : u64), (0 : u64), (1 : u64)])
    (y := #v[(0 : u64), (0 : u64), (0 : u64), (1 : u64)])
    (z := #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)])))

--  Check if a point is the identity (Z == 0).
def point_is_identity (p : P256Point) : RustM Bool := do
  (Core_models.Cmp.PartialEq.eq
    (RustArray u64 4)
    (RustArray u64 4)
    (P256Point.z p)
    #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)])

--  The standard base point G.
def base_point (_ : Rust_primitives.Hax.Tuple0) : RustM P256Point := do
  (pure (P256Point.mk
    (x := P256_GX)
    (y := P256_GY)
    (z := #v[(0 : u64), (0 : u64), (0 : u64), (1 : u64)])))

--  Point doubling in Jacobian coordinates.
-- 
--  Using the formula from "Guide to Elliptic Curve Cryptography" (Hankerson et al.),
--  Algorithm 3.21, specialised for a = -3.
-- 
--  Input: P = (X1, Y1, Z1)
--  Output: 2P = (X3, Y3, Z3)
-- 
--  If Y1 == 0 or P is identity, return identity.
-- 
--    S = 4 * X1 * Y1^2
--    M = 3 * X1^2 + a * Z1^4  (with a = -3: M = 3*(X1 - Z1^2)*(X1 + Z1^2))
--    X3 = M^2 - 2*S
--    Y3 = M*(S - X3) - 8*Y1^4
--    Z3 = 2*Y1*Z1
def point_double (p : P256Point) : RustM P256Point := do
  if (← (point_is_identity p)) then
    (point_identity Rust_primitives.Hax.Tuple0.mk)
  else
    let x1 : (RustArray u64 4) := (P256Point.x p);
    let y1 : (RustArray u64 4) := (P256Point.y p);
    let z1 : (RustArray u64 4) := (P256Point.z p);
    let y1_sq : (RustArray u64 4) ← (fp_sq y1);
    let four : (RustArray u64 4) :=
      #v[(0 : u64), (0 : u64), (0 : u64), (4 : u64)];
    let s : (RustArray u64 4) ← (fp_mul four (← (fp_mul x1 y1_sq)));
    let z1_sq : (RustArray u64 4) ← (fp_sq z1);
    let three : (RustArray u64 4) :=
      #v[(0 : u64), (0 : u64), (0 : u64), (3 : u64)];
    let m : (RustArray u64 4) ←
      (fp_mul three (← (fp_mul (← (fp_sub x1 z1_sq)) (← (fp_add x1 z1_sq)))));
    let m_sq : (RustArray u64 4) ← (fp_sq m);
    let two_s : (RustArray u64 4) ← (fp_add s s);
    let x3 : (RustArray u64 4) ← (fp_sub m_sq two_s);
    let eight : (RustArray u64 4) :=
      #v[(0 : u64), (0 : u64), (0 : u64), (8 : u64)];
    let y1_4 : (RustArray u64 4) ← (fp_sq y1_sq);
    let y3 : (RustArray u64 4) ←
      (fp_sub (← (fp_mul m (← (fp_sub s x3)))) (← (fp_mul eight y1_4)));
    let two : (RustArray u64 4) :=
      #v[(0 : u64), (0 : u64), (0 : u64), (2 : u64)];
    let z3 : (RustArray u64 4) ← (fp_mul two (← (fp_mul y1 z1)));
    (pure (P256Point.mk (x := x3) (y := y3) (z := z3)))

--  Point addition in Jacobian coordinates.
-- 
--  Using mixed Jacobian addition when one point has Z=1 is a special case;
--  this is the general formula.
-- 
--  Input: P = (X1,Y1,Z1), Q = (X2,Y2,Z2)
--  Output: P + Q
-- 
--    U1 = X1*Z2^2, U2 = X2*Z1^2
--    S1 = Y1*Z2^3, S2 = Y2*Z1^3
--    H = U2 - U1, R = S2 - S1
--    If H == 0 and R == 0: return point_double(P)
--    If H == 0 and R != 0: return identity (P = -Q)
--    X3 = R^2 - H^3 - 2*U1*H^2
--    Y3 = R*(U1*H^2 - X3) - S1*H^3
--    Z3 = H*Z1*Z2
def point_add (p : P256Point) (q : P256Point) : RustM P256Point := do
  if (← (point_is_identity p)) then
    (pure q)
  else
    if (← (point_is_identity q)) then
      (pure p)
    else
      let z1_sq : (RustArray u64 4) ← (fp_sq (P256Point.z p));
      let z2_sq : (RustArray u64 4) ← (fp_sq (P256Point.z q));
      let z1_cu : (RustArray u64 4) ← (fp_mul z1_sq (P256Point.z p));
      let z2_cu : (RustArray u64 4) ← (fp_mul z2_sq (P256Point.z q));
      let u1 : (RustArray u64 4) ← (fp_mul (P256Point.x p) z2_sq);
      let u2 : (RustArray u64 4) ← (fp_mul (P256Point.x q) z1_sq);
      let s1 : (RustArray u64 4) ← (fp_mul (P256Point.y p) z2_cu);
      let s2 : (RustArray u64 4) ← (fp_mul (P256Point.y q) z1_cu);
      let h : (RustArray u64 4) ← (fp_sub u2 u1);
      let r : (RustArray u64 4) ← (fp_sub s2 s1);
      let zero : (RustArray u64 4) :=
        #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)];
      if
      (← (Core_models.Cmp.PartialEq.eq
        (RustArray u64 4)
        (RustArray u64 4) h zero)) then
        if
        (← (Core_models.Cmp.PartialEq.eq
          (RustArray u64 4)
          (RustArray u64 4) r zero)) then
          (point_double p)
        else
          (point_identity Rust_primitives.Hax.Tuple0.mk)
      else
        let h_sq : (RustArray u64 4) ← (fp_sq h);
        let h_cu : (RustArray u64 4) ← (fp_mul h_sq h);
        let r_sq : (RustArray u64 4) ← (fp_sq r);
        let two : (RustArray u64 4) :=
          #v[(0 : u64), (0 : u64), (0 : u64), (2 : u64)];
        let u1_h_sq : (RustArray u64 4) ← (fp_mul u1 h_sq);
        let x3 : (RustArray u64 4) ←
          (fp_sub (← (fp_sub r_sq h_cu)) (← (fp_mul two u1_h_sq)));
        let y3 : (RustArray u64 4) ←
          (fp_sub (← (fp_mul r (← (fp_sub u1_h_sq x3)))) (← (fp_mul s1 h_cu)));
        let z3 : (RustArray u64 4) ←
          (fp_mul h (← (fp_mul (P256Point.z p) (P256Point.z q))));
        (pure (P256Point.mk (x := x3) (y := y3) (z := z3)))

--  Scalar multiplication: k * P using double-and-add (left-to-right binary).
def scalar_mult (k : (RustArray u8 32)) (p : P256Point) : RustM P256Point := do
  let result : P256Point ← (point_identity Rust_primitives.Hax.Tuple0.mk);
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (256 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : P256Point ← (point_double result);
        let byte_idx : usize ← (i /? (8 : usize));
        let bit_idx : usize ← ((7 : usize) -? (← (i %? (8 : usize))));
        let result : P256Point ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← ((← k[byte_idx]_?) >>>? bit_idx)) &&&? (1 : u8)))
            (1 : u8))) then
            let result : P256Point ← (point_add result p);
            (pure result)
          else
            (pure result);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize P256Point))));
  (pure result)

--  Base point multiplication: k * G.
def base_mult (k : (RustArray u8 32)) : RustM P256Point := do
  let g : P256Point ← (base_point Rust_primitives.Hax.Tuple0.mk);
  (scalar_mult k g)

--  Convert Jacobian coordinates to affine (x, y) and encode as uncompressed.
--  Returns 0x04 || x (32 bytes BE) || y (32 bytes BE) = 65 bytes.
def point_to_uncompressed (p : P256Point) : RustM (RustArray u8 65) := do
  let out : (RustArray u8 65) ←
    (Rust_primitives.Hax.repeat (0 : u8) (65 : usize));
  if (← (point_is_identity p)) then
    let out : (RustArray u8 65) ←
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        out
        (0 : usize)
        (4 : u8));
    (pure out)
  else
    let z_inv : (RustArray u64 4) ← (fp_inv (P256Point.z p));
    let z_inv_sq : (RustArray u64 4) ← (fp_sq z_inv);
    let z_inv_cu : (RustArray u64 4) ← (fp_mul z_inv_sq z_inv);
    let x : (RustArray u64 4) ← (fp_mul (P256Point.x p) z_inv_sq);
    let y : (RustArray u64 4) ← (fp_mul (P256Point.y p) z_inv_cu);
    let out : (RustArray u8 65) ←
      (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
        out
        (0 : usize)
        (4 : u8));
    let xb : (RustArray u8 32) ← (fp_to_bytes x);
    let yb : (RustArray u8 32) ← (fp_to_bytes y);
    let j : usize := (0 : usize);
    let ⟨j, out⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨j, out⟩ => (do (pure true) : RustM Bool))
        (fun ⟨j, out⟩ =>
          (do (Rust_primitives.Hax.Machine_int.lt j (32 : usize)) : RustM Bool))
        (fun ⟨j, out⟩ =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple2.mk j out)
        (fun ⟨j, out⟩ =>
          (do
          let out : (RustArray u8 65) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              (← ((1 : usize) +? j))
              (← xb[j]_?));
          let out : (RustArray u8 65) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              out
              (← ((33 : usize) +? j))
              (← yb[j]_?));
          let j : usize ← (j +? (1 : usize));
          (pure (Rust_primitives.Hax.Tuple2.mk j out)) :
          RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 65)))));
    (pure out)

--  Decode a 65-byte uncompressed point (0x04 || x || y).
--  Returns None if the prefix is wrong or the point is not on the curve.
def point_from_uncompressed (bytes : (RustArray u8 65)) :
    RustM (Core_models.Option.Option P256Point) := do
  if
  (← (Rust_primitives.Hax.Machine_int.ne (← bytes[(0 : usize)]_?) (4 : u8)))
  then
    (pure Core_models.Option.Option.None)
  else
    let xb : (RustArray u8 32) ←
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    let yb : (RustArray u8 32) ←
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    let i : usize := (0 : usize);
    let ⟨i, xb, yb⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨i, xb, yb⟩ => (do (pure true) : RustM Bool))
        (fun ⟨i, xb, yb⟩ =>
          (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
        (fun ⟨i, xb, yb⟩ =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple3.mk i xb yb)
        (fun ⟨i, xb, yb⟩ =>
          (do
          let xb : (RustArray u8 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              xb
              i
              (← bytes[(← ((1 : usize) +? i))]_?));
          let yb : (RustArray u8 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              yb
              i
              (← bytes[(← ((33 : usize) +? i))]_?));
          let i : usize ← (i +? (1 : usize));
          (pure (Rust_primitives.Hax.Tuple3.mk i xb yb)) :
          RustM
          (Rust_primitives.Hax.Tuple3
            usize
            (RustArray u8 32)
            (RustArray u8 32)))));
    let x : (RustArray u64 4) ← (fp_from_bytes xb);
    let y : (RustArray u64 4) ← (fp_from_bytes yb);
    let y_sq : (RustArray u64 4) ← (fp_sq y);
    let x_sq : (RustArray u64 4) ← (fp_sq x);
    let x_cu : (RustArray u64 4) ← (fp_mul x_sq x);
    let three_x : (RustArray u64 4) ←
      (fp_mul #v[(0 : u64), (0 : u64), (0 : u64), (3 : u64)] x);
    let rhs : (RustArray u64 4) ← (fp_add (← (fp_sub x_cu three_x)) P256_B);
    if
    (← (Core_models.Cmp.PartialEq.ne
      (RustArray u64 4)
      (RustArray u64 4) y_sq rhs)) then
      (pure Core_models.Option.Option.None)
    else
      (pure (Core_models.Option.Option.Some
        (P256Point.mk
          (x := x)
          (y := y)
          (z := #v[(0 : u64), (0 : u64), (0 : u64), (1 : u64)]))))

--  Get the affine x-coordinate of a point as a field element.
--  Returns [0,0,0,0] for the point at infinity.
def point_affine_x (p : P256Point) : RustM (RustArray u64 4) := do
  if (← (point_is_identity p)) then
    (pure #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)])
  else
    let z_inv : (RustArray u64 4) ← (fp_inv (P256Point.z p));
    let z_inv_sq : (RustArray u64 4) ← (fp_sq z_inv);
    (fp_mul (P256Point.x p) z_inv_sq)

--  Get the affine y-coordinate of a point as a field element.
def point_affine_y (p : P256Point) : RustM (RustArray u64 4) := do
  if (← (point_is_identity p)) then
    (pure #v[(0 : u64), (0 : u64), (0 : u64), (0 : u64)])
  else
    let z_inv : (RustArray u64 4) ← (fp_inv (P256Point.z p));
    let z_inv_cu : (RustArray u64 4) ← (fp_mul (← (fp_sq z_inv)) z_inv);
    (fp_mul (P256Point.y p) z_inv_cu)

end Libcrux_specs_hax.P256


namespace Libcrux_specs_hax.Edwards25519

--  A point on the Edwards25519 curve in extended coordinates.
structure EdPoint where
  x : (RustArray u64 5)
  y : (RustArray u64 5)
  z : (RustArray u64 5)
  t : (RustArray u64 5)

@[instance] opaque Impl.AssociatedTypes :
  Core_models.Clone.Clone.AssociatedTypes EdPoint :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl :
  Core_models.Clone.Clone EdPoint :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1.AssociatedTypes :
  Core_models.Marker.Copy.AssociatedTypes EdPoint :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_1 :
  Core_models.Marker.Copy EdPoint :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2.AssociatedTypes :
  Core_models.Fmt.Debug.AssociatedTypes EdPoint :=
  by constructor <;> exact Inhabited.default

@[instance] opaque Impl_2 :
  Core_models.Fmt.Debug EdPoint :=
  by constructor <;> exact Inhabited.default

--  The curve parameter d = -121665/121666 mod p.
-- 
--  d = 37095705934669439343138083508754565189542113879843219016388785533085940283555
-- 
--  In 51-bit limbs:
def ed_d (_ : Rust_primitives.Hax.Tuple0) : RustM (RustArray u64 5) := do
  let d_bytes : (RustArray u8 32) :=
    #v[(163 : u8),
         (120 : u8),
         (89 : u8),
         (19 : u8),
         (202 : u8),
         (77 : u8),
         (235 : u8),
         (117 : u8),
         (171 : u8),
         (216 : u8),
         (65 : u8),
         (65 : u8),
         (77 : u8),
         (10 : u8),
         (112 : u8),
         (0 : u8),
         (152 : u8),
         (232 : u8),
         (121 : u8),
         (119 : u8),
         (121 : u8),
         (64 : u8),
         (199 : u8),
         (140 : u8),
         (115 : u8),
         (254 : u8),
         (111 : u8),
         (43 : u8),
         (238 : u8),
         (108 : u8),
         (3 : u8),
         (82 : u8)];
  (Libcrux_specs_hax.Curve25519.fe_from_bytes d_bytes)

--  2*d, precomputed for the addition formula.
def ed_2d (_ : Rust_primitives.Hax.Tuple0) : RustM (RustArray u64 5) := do
  let d : (RustArray u64 5) ← (ed_d Rust_primitives.Hax.Tuple0.mk);
  (Libcrux_specs_hax.Curve25519.fe_add d d)

--  The identity point (neutral element): (0, 1, 1, 0).
def point_identity (_ : Rust_primitives.Hax.Tuple0) : RustM EdPoint := do
  (pure (EdPoint.mk
    (x := (← (Libcrux_specs_hax.Curve25519.fe_zero
      Rust_primitives.Hax.Tuple0.mk)))
    (y := (← (Libcrux_specs_hax.Curve25519.fe_one
      Rust_primitives.Hax.Tuple0.mk)))
    (z := (← (Libcrux_specs_hax.Curve25519.fe_one
      Rust_primitives.Hax.Tuple0.mk)))
    (t := (← (Libcrux_specs_hax.Curve25519.fe_zero
      Rust_primitives.Hax.Tuple0.mk)))))

--  The Edwards25519 base point B.
-- 
--  Bx = 15112221349535807912866137220509078750507884956996801397853916694561507378526
--  By = 46316835694926478169428394003475163141307993866256225615783033890098355573398
def ed25519_base_point (_ : Rust_primitives.Hax.Tuple0) : RustM EdPoint := do
  let bx_bytes : (RustArray u8 32) :=
    #v[(26 : u8),
         (213 : u8),
         (37 : u8),
         (143 : u8),
         (96 : u8),
         (45 : u8),
         (86 : u8),
         (201 : u8),
         (178 : u8),
         (167 : u8),
         (37 : u8),
         (149 : u8),
         (96 : u8),
         (199 : u8),
         (44 : u8),
         (105 : u8),
         (92 : u8),
         (220 : u8),
         (214 : u8),
         (253 : u8),
         (49 : u8),
         (226 : u8),
         (164 : u8),
         (192 : u8),
         (254 : u8),
         (83 : u8),
         (110 : u8),
         (205 : u8),
         (211 : u8),
         (54 : u8),
         (105 : u8),
         (33 : u8)];
  let by_bytes : (RustArray u8 32) :=
    #v[(88 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8),
         (102 : u8)];
  let x : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_from_bytes bx_bytes);
  let y : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_from_bytes by_bytes);
  let z : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_one Rust_primitives.Hax.Tuple0.mk);
  let t : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul x y);
  (pure (EdPoint.mk (x := x) (y := y) (z := z) (t := t)))

--  Unified point addition for extended coordinates (RFC 8032 / EFD).
-- 
--  Input: P1 = (X1, Y1, Z1, T1), P2 = (X2, Y2, Z2, T2)
--  Output: P1 + P2 = (X3, Y3, Z3, T3)
-- 
--  Using the formula from Hisil et al. (2008):
--    A = (Y1 - X1) * (Y2 - X2)
--    B = (Y1 + X1) * (Y2 + X2)
--    C = T1 * 2*d * T2
--    D = Z1 * 2 * Z2
--    E = B - A
--    F = D - C
--    G = D + C
--    H = B + A
--    X3 = E * F
--    Y3 = G * H
--    T3 = E * H
--    Z3 = F * G
def point_add (p1 : EdPoint) (p2 : EdPoint) : RustM EdPoint := do
  let two_d : (RustArray u64 5) ← (ed_2d Rust_primitives.Hax.Tuple0.mk);
  let a : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul
      (← (Libcrux_specs_hax.Curve25519.fe_sub (EdPoint.y p1) (EdPoint.x p1)))
      (← (Libcrux_specs_hax.Curve25519.fe_sub (EdPoint.y p2) (EdPoint.x p2))));
  let b : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul
      (← (Libcrux_specs_hax.Curve25519.fe_add (EdPoint.y p1) (EdPoint.x p1)))
      (← (Libcrux_specs_hax.Curve25519.fe_add (EdPoint.y p2) (EdPoint.x p2))));
  let c : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul
      (← (Libcrux_specs_hax.Curve25519.fe_mul (EdPoint.t p1) two_d))
      (EdPoint.t p2));
  let d : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul
      (← (Libcrux_specs_hax.Curve25519.fe_add (EdPoint.z p1) (EdPoint.z p1)))
      (EdPoint.z p2));
  let e : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sub b a);
  let f : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sub d c);
  let g : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_add d c);
  let h : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_add b a);
  let x3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul e f);
  let y3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul g h);
  let t3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul e h);
  let z3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul f g);
  (pure (EdPoint.mk (x := x3) (y := y3) (z := z3) (t := t3)))

--  Point doubling for extended coordinates (dbl-2008-hwcd with a = -1).
-- 
--    A = X1^2
--    B = Y1^2
--    C = 2 * Z1^2
--    D = a * A = -A  (since a = -1 for Ed25519)
--    E = (X1 + Y1)^2 - A - B
--    G = D + B
--    F = G - C
--    H = D - B
--    X3 = E * F
--    Y3 = G * H
--    T3 = E * H
--    Z3 = F * G
def point_double (p : EdPoint) : RustM EdPoint := do
  let aa : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_sq (EdPoint.x p));
  let b : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_sq (EdPoint.y p));
  let c : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_add
      (← (Libcrux_specs_hax.Curve25519.fe_sq (EdPoint.z p)))
      (← (Libcrux_specs_hax.Curve25519.fe_sq (EdPoint.z p))));
  let d : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_sub
      (← (Libcrux_specs_hax.Curve25519.fe_zero Rust_primitives.Hax.Tuple0.mk))
      aa);
  let xy_sum : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_add (EdPoint.x p) (EdPoint.y p));
  let e : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_sub
      (← (Libcrux_specs_hax.Curve25519.fe_sub
        (← (Libcrux_specs_hax.Curve25519.fe_sq xy_sum))
        aa))
      b);
  let g : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_add d b);
  let f : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sub g c);
  let h : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sub d b);
  let x3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul e f);
  let y3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul g h);
  let t3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul e h);
  let z3 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul f g);
  (pure (EdPoint.mk (x := x3) (y := y3) (z := z3) (t := t3)))

--  Scalar multiplication: scalar * point using double-and-add.
--  The scalar is a 256-bit little-endian byte string.
def scalar_mult (scalar : (RustArray u8 32)) (point : EdPoint) :
    RustM EdPoint := do
  let result : EdPoint ← (point_identity Rust_primitives.Hax.Tuple0.mk);
  let i : i32 := (255 : i32);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.ge i (0 : i32)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let result : EdPoint ← (point_double result);
        let byte_idx : usize ←
          (Rust_primitives.Hax.cast_op (← (i /? (8 : i32))));
        let bit_idx : u32 ← (Rust_primitives.Hax.cast_op (← (i %? (8 : i32))));
        let result : EdPoint ←
          if
          (← (Rust_primitives.Hax.Machine_int.eq
            (← ((← ((← scalar[byte_idx]_?) >>>? bit_idx)) &&&? (1 : u8)))
            (1 : u8))) then
            let result : EdPoint ← (point_add result point);
            (pure result)
          else
            (pure result);
        let i : i32 ← (i -? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 i32 EdPoint))));
  (pure result)

--  Encode a point to 32 bytes per RFC 8032.
-- 
--  The encoding is the y-coordinate (little-endian, 255 bits) with the
--  sign bit of x stored in the top bit (bit 255).
def point_encode (p : EdPoint) : RustM (RustArray u8 32) := do
  let z_inv : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_inv (EdPoint.z p));
  let x : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_reduce
      (← (Libcrux_specs_hax.Curve25519.fe_mul (EdPoint.x p) z_inv)));
  let y : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul (EdPoint.y p) z_inv);
  let enc : (RustArray u8 32) ← (Libcrux_specs_hax.Curve25519.fe_to_bytes y);
  let x_bytes : (RustArray u8 32) ←
    (Libcrux_specs_hax.Curve25519.fe_to_bytes x);
  let enc : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      enc
      (31 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← enc[(31 : usize)]_?)
        (← ((← ((← x_bytes[(0 : usize)]_?) &&&? (1 : u8))) <<<? (7 : i32))))));
  (pure enc)

--  Compute a^(2^n) by repeated squaring.
def fe_sq_n (a : (RustArray u64 5)) (n : u32) : RustM (RustArray u64 5) := do
  let r : (RustArray u64 5) := a;
  let i : u32 := (0 : u32);
  let ⟨i, r⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, r⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, r⟩ => (do (Rust_primitives.Hax.Machine_int.lt i n) : RustM Bool))
      (fun ⟨i, r⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i r)
      (fun ⟨i, r⟩ =>
        (do
        let r : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq r);
        let i : u32 ← (i +? (1 : u32));
        (pure (Rust_primitives.Hax.Tuple2.mk i r)) :
        RustM (Rust_primitives.Hax.Tuple2 u32 (RustArray u64 5)))));
  (pure r)

--  Compute a^((p-5)/8) = a^(2^252 - 3) using a standard addition chain.
def pow252m3 (z : (RustArray u64 5)) : RustM (RustArray u64 5) := do
  let z1 : (RustArray u64 5) := z;
  let z2 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq z1);
  let t : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq z2);
  let t : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq t);
  let z9 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul t z1);
  let z11 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul z9 z2);
  let t : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq z11);
  let z_5_0 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul t z9);
  let z_10_5 : (RustArray u64 5) ← (fe_sq_n z_5_0 (5 : u32));
  let z_10_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_10_5 z_5_0);
  let z_20_10 : (RustArray u64 5) ← (fe_sq_n z_10_0 (10 : u32));
  let z_20_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_20_10 z_10_0);
  let z_40_20 : (RustArray u64 5) ← (fe_sq_n z_20_0 (20 : u32));
  let z_40_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_40_20 z_20_0);
  let z_50_10 : (RustArray u64 5) ← (fe_sq_n z_40_0 (10 : u32));
  let z_50_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_50_10 z_10_0);
  let z_100_50 : (RustArray u64 5) ← (fe_sq_n z_50_0 (50 : u32));
  let z_100_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_100_50 z_50_0);
  let z_200_100 : (RustArray u64 5) ← (fe_sq_n z_100_0 (100 : u32));
  let z_200_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_200_100 z_100_0);
  let z_250_50 : (RustArray u64 5) ← (fe_sq_n z_200_0 (50 : u32));
  let z_250_0 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul z_250_50 z_50_0);
  let z_252_2 : (RustArray u64 5) ← (fe_sq_n z_250_0 (2 : u32));
  (Libcrux_specs_hax.Curve25519.fe_mul z_252_2 z1)

--  Decode a 32-byte encoding to a point per RFC 8032.
-- 
--  1. Extract y from bits 0..254, the sign bit from bit 255.
--  2. Compute x^2 = (y^2 - 1) / (d*y^2 + 1) mod p.
--  3. Compute x = sqrt(x^2) using x = (x^2)^((p+3)/8) mod p.
--  4. Adjust sign of x.
-- 
--  Returns None if the encoding is invalid (no square root exists).
def point_decode (bytes : (RustArray u8 32)) :
    RustM (Core_models.Option.Option EdPoint) := do
  let x_sign : u8 ←
    ((← ((← bytes[(31 : usize)]_?) >>>? (7 : i32))) &&&? (1 : u8));
  let y_bytes : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨i, y_bytes⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, y_bytes⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, y_bytes⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, y_bytes⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i y_bytes)
      (fun ⟨i, y_bytes⟩ =>
        (do
        let y_bytes : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            y_bytes
            i
            (← bytes[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i y_bytes)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  let y_bytes : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      y_bytes
      (31 : usize)
      (← ((← y_bytes[(31 : usize)]_?) &&&? (127 : u8))));
  let y : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_from_bytes y_bytes);
  let y_sq : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq y);
  let d : (RustArray u64 5) ← (ed_d Rust_primitives.Hax.Tuple0.mk);
  let u : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_sub
      y_sq
      (← (Libcrux_specs_hax.Curve25519.fe_one Rust_primitives.Hax.Tuple0.mk)));
  let v : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_add
      (← (Libcrux_specs_hax.Curve25519.fe_mul d y_sq))
      (← (Libcrux_specs_hax.Curve25519.fe_one Rust_primitives.Hax.Tuple0.mk)));
  let v_sq : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq v);
  let v_cu : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul v_sq v);
  let v4 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_sq v_sq);
  let v7 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul v4 v_cu);
  let uv7 : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul u v7);
  let exp : (RustArray u64 5) ← (pow252m3 uv7);
  let x : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul
      (← (Libcrux_specs_hax.Curve25519.fe_mul u v_cu))
      exp);
  let vx_sq : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_mul
      v
      (← (Libcrux_specs_hax.Curve25519.fe_sq x)));
  let check : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_reduce
      (← (Libcrux_specs_hax.Curve25519.fe_sub vx_sq u)));
  let check_neg : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_reduce
      (← (Libcrux_specs_hax.Curve25519.fe_sub
        vx_sq
        (← (Libcrux_specs_hax.Curve25519.fe_sub
          (← (Libcrux_specs_hax.Curve25519.fe_zero
            Rust_primitives.Hax.Tuple0.mk))
          u)))));
  let sqrt_m1 : (RustArray u64 5) ←
    (Libcrux_specs_hax.Curve25519.fe_from_bytes
      #v[(176 : u8),
           (160 : u8),
           (14 : u8),
           (74 : u8),
           (39 : u8),
           (27 : u8),
           (238 : u8),
           (196 : u8),
           (120 : u8),
           (228 : u8),
           (47 : u8),
           (173 : u8),
           (6 : u8),
           (24 : u8),
           (67 : u8),
           (47 : u8),
           (167 : u8),
           (215 : u8),
           (251 : u8),
           (61 : u8),
           (153 : u8),
           (0 : u8),
           (77 : u8),
           (43 : u8),
           (11 : u8),
           (223 : u8),
           (193 : u8),
           (79 : u8),
           (128 : u8),
           (36 : u8),
           (131 : u8),
           (43 : u8)]);
  let is_zero : ((RustArray u64 5) -> RustM Bool) :=
    (fun a =>
      (do
      let r : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_reduce a);
      ((← ((← ((← ((← (Rust_primitives.Hax.Machine_int.eq
                (← r[(0 : usize)]_?)
                (0 : u64)))
              &&? (← (Rust_primitives.Hax.Machine_int.eq
                (← r[(1 : usize)]_?)
                (0 : u64)))))
            &&? (← (Rust_primitives.Hax.Machine_int.eq
              (← r[(2 : usize)]_?)
              (0 : u64)))))
          &&? (← (Rust_primitives.Hax.Machine_int.eq
            (← r[(3 : usize)]_?)
            (0 : u64)))))
        &&? (← (Rust_primitives.Hax.Machine_int.eq
          (← r[(4 : usize)]_?)
          (0 : u64)))) :
      RustM Bool));
  if
  (← (Core_models.Ops.Function.Fn.call
    ((RustArray u64 5) -> RustM Bool)
    (Rust_primitives.Hax.Tuple1 (RustArray u64 5))
    is_zero
    (Rust_primitives.Hax.Tuple1.mk check))) then
    let x_reduced : (RustArray u64 5) ←
      (Libcrux_specs_hax.Curve25519.fe_reduce x);
    let x_bytes : (RustArray u8 32) ←
      (Libcrux_specs_hax.Curve25519.fe_to_bytes x_reduced);
    let x_low_bit : u8 ← ((← x_bytes[(0 : usize)]_?) &&&? (1 : u8));
    let x : (RustArray u64 5) ←
      if (← (Rust_primitives.Hax.Machine_int.ne x_low_bit x_sign)) then
        let x : (RustArray u64 5) ←
          (Libcrux_specs_hax.Curve25519.fe_sub
            (← (Libcrux_specs_hax.Curve25519.fe_zero
              Rust_primitives.Hax.Tuple0.mk))
            x);
        (pure x)
      else
        (pure x);
    let x_red : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_reduce x);
    if
    (← ((← (Rust_primitives.Hax.Machine_int.eq x_sign (1 : u8)))
      &&? (← (Core_models.Ops.Function.Fn.call
        ((RustArray u64 5) -> RustM Bool)
        (Rust_primitives.Hax.Tuple1 (RustArray u64 5))
        is_zero
        (Rust_primitives.Hax.Tuple1.mk x_red))))) then
      (pure Core_models.Option.Option.None)
    else
      let z : (RustArray u64 5) ←
        (Libcrux_specs_hax.Curve25519.fe_one Rust_primitives.Hax.Tuple0.mk);
      let t : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul x y);
      (pure (Core_models.Option.Option.Some
        (EdPoint.mk (x := x) (y := y) (z := z) (t := t))))
  else
    if
    (← (Core_models.Ops.Function.Fn.call
      ((RustArray u64 5) -> RustM Bool)
      (Rust_primitives.Hax.Tuple1 (RustArray u64 5))
      is_zero
      (Rust_primitives.Hax.Tuple1.mk check_neg))) then
      let x : (RustArray u64 5) ←
        (Libcrux_specs_hax.Curve25519.fe_mul x sqrt_m1);
      let x_reduced : (RustArray u64 5) ←
        (Libcrux_specs_hax.Curve25519.fe_reduce x);
      let x_bytes : (RustArray u8 32) ←
        (Libcrux_specs_hax.Curve25519.fe_to_bytes x_reduced);
      let x_low_bit : u8 ← ((← x_bytes[(0 : usize)]_?) &&&? (1 : u8));
      let x : (RustArray u64 5) ←
        if (← (Rust_primitives.Hax.Machine_int.ne x_low_bit x_sign)) then
          let x : (RustArray u64 5) ←
            (Libcrux_specs_hax.Curve25519.fe_sub
              (← (Libcrux_specs_hax.Curve25519.fe_zero
                Rust_primitives.Hax.Tuple0.mk))
              x);
          (pure x)
        else
          (pure x);
      let x_red : (RustArray u64 5) ←
        (Libcrux_specs_hax.Curve25519.fe_reduce x);
      if
      (← ((← (Rust_primitives.Hax.Machine_int.eq x_sign (1 : u8)))
        &&? (← (Core_models.Ops.Function.Fn.call
          ((RustArray u64 5) -> RustM Bool)
          (Rust_primitives.Hax.Tuple1 (RustArray u64 5))
          is_zero
          (Rust_primitives.Hax.Tuple1.mk x_red))))) then
        (pure Core_models.Option.Option.None)
      else
        let z : (RustArray u64 5) ←
          (Libcrux_specs_hax.Curve25519.fe_one Rust_primitives.Hax.Tuple0.mk);
        let t : (RustArray u64 5) ← (Libcrux_specs_hax.Curve25519.fe_mul x y);
        (pure (Core_models.Option.Option.Some
          (EdPoint.mk (x := x) (y := y) (z := z) (t := t))))
    else
      (pure Core_models.Option.Option.None)

--  Check if acc >= L (acc is 5 words, L is 4 words, both little-endian).
def ge_l (acc : (RustArray u64 5)) (l : (RustArray u64 4)) : RustM Bool := do
  if
  (← (Rust_primitives.Hax.Machine_int.gt (← acc[(4 : usize)]_?) (0 : u64))) then
    (pure true)
  else
    let i : usize := (4 : usize);
    match
      (← (Rust_primitives.Hax.while_loop_return
        (fun i => (do (pure true) : RustM Bool))
        (fun i =>
          (do (Rust_primitives.Hax.Machine_int.gt i (0 : usize)) : RustM Bool))
        (fun i =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        i
        (fun i =>
          (do
          let i : usize ← (i -? (1 : usize));
          if
          (← (Rust_primitives.Hax.Machine_int.gt (← acc[i]_?) (← l[i]_?))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Core_models.Ops.Control_flow.ControlFlow.Break true)))
          else
            if
            (← (Rust_primitives.Hax.Machine_int.lt (← acc[i]_?) (← l[i]_?)))
            then
              (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                (Core_models.Ops.Control_flow.ControlFlow.Break false)))
            else
              (pure (Core_models.Ops.Control_flow.ControlFlow.Continue i)) :
          RustM
          (Core_models.Ops.Control_flow.ControlFlow
            (Core_models.Ops.Control_flow.ControlFlow
              Bool
              (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 usize))
            usize)))))
    with
      | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
      | (Core_models.Ops.Control_flow.ControlFlow.Continue  i) => (pure true)

--  Subtract L from acc (acc -= L). acc is 5 words, L is 4 words (little-endian).
def sub_l (acc : (RustArray u64 5)) (l : (RustArray u64 4)) :
    RustM (RustArray u64 5) := do
  let borrow : u64 := (0 : u64);
  let i : usize := (0 : usize);
  let ⟨acc, borrow, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, borrow, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, borrow, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun ⟨acc, borrow, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk acc borrow i)
      (fun ⟨acc, borrow, i⟩ =>
        (do
        let ⟨r, b1⟩ ←
          (Core_models.Num.Impl_9.overflowing_sub (← acc[i]_?) (← l[i]_?));
        let ⟨r2, b2⟩ ← (Core_models.Num.Impl_9.overflowing_sub r borrow);
        let acc : (RustArray u64 5) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            i
            r2);
        let borrow : u64 ←
          ((← (Rust_primitives.Hax.cast_op b1))
            +? (← (Rust_primitives.Hax.cast_op b2)));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple3.mk acc borrow i)) :
        RustM (Rust_primitives.Hax.Tuple3 (RustArray u64 5) u64 usize))));
  let acc : (RustArray u64 5) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      acc
      (4 : usize)
      (← (Core_models.Num.Impl_9.wrapping_sub (← acc[(4 : usize)]_?) borrow)));
  (pure acc)

--  Reduce a 512-bit little-endian scalar mod L, where
--  L = 2^252 + 27742317777372353535851937790883648493.
-- 
--  Input: 64-byte little-endian integer.
--  Output: 32-byte little-endian integer in [0, L).
def scalar_reduce (s : (RustArray u8 64)) : RustM (RustArray u8 32) := do
  let l_bytes : (RustArray u8 32) :=
    #v[(237 : u8),
         (211 : u8),
         (245 : u8),
         (92 : u8),
         (26 : u8),
         (99 : u8),
         (18 : u8),
         (88 : u8),
         (214 : u8),
         (156 : u8),
         (247 : u8),
         (162 : u8),
         (222 : u8),
         (249 : u8),
         (222 : u8),
         (20 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (0 : u8),
         (16 : u8)];
  let s_words : (RustArray u64 8) ←
    (Rust_primitives.Hax.repeat (0 : u64) (8 : usize));
  let i : usize := (0 : usize);
  let ⟨i, s_words⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, s_words⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, s_words⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (8 : usize)) : RustM Bool))
      (fun ⟨i, s_words⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i s_words)
      (fun ⟨i, s_words⟩ =>
        (do
        let base : usize ← (i *? (8 : usize));
        let w : u64 := (0 : u64);
        let j : usize := (0 : usize);
        let ⟨j, w⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, w⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, w⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, w⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j w)
            (fun ⟨j, w⟩ =>
              (do
              let w : u64 ←
                (Rust_primitives.Hax.Machine_int.bitor
                  w
                  (← ((← (Rust_primitives.Hax.cast_op (← s[(← (base +? j))]_?)))
                    <<<? (← ((8 : usize) *? j)))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j w)) :
              RustM (Rust_primitives.Hax.Tuple2 usize u64))));
        let s_words : (RustArray u64 8) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            s_words
            i
            w);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i s_words)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 8)))));
  let l_words : (RustArray u64 4) ←
    (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
  let i : usize := (0 : usize);
  let ⟨i, l_words⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, l_words⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, l_words⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun ⟨i, l_words⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i l_words)
      (fun ⟨i, l_words⟩ =>
        (do
        let base : usize ← (i *? (8 : usize));
        let w : u64 := (0 : u64);
        let j : usize := (0 : usize);
        let ⟨j, w⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, w⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, w⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, w⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j w)
            (fun ⟨j, w⟩ =>
              (do
              let w : u64 ←
                (Rust_primitives.Hax.Machine_int.bitor
                  w
                  (← ((← (Rust_primitives.Hax.cast_op
                      (← l_bytes[(← (base +? j))]_?)))
                    <<<? (← ((8 : usize) *? j)))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j w)) :
              RustM (Rust_primitives.Hax.Tuple2 usize u64))));
        let l_words : (RustArray u64 4) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            l_words
            i
            w);
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i l_words)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u64 4)))));
  let acc : (RustArray u64 5) ←
    (Rust_primitives.Hax.repeat (0 : u64) (5 : usize));
  let bit : i32 := (511 : i32);
  let ⟨acc, bit⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨acc, bit⟩ => (do (pure true) : RustM Bool))
      (fun ⟨acc, bit⟩ =>
        (do (Rust_primitives.Hax.Machine_int.ge bit (0 : i32)) : RustM Bool))
      (fun ⟨acc, bit⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk acc bit)
      (fun ⟨acc, bit⟩ =>
        (do
        let carry : u64 := (0 : u64);
        let k : usize := (0 : usize);
        let ⟨acc, carry, k⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨acc, carry, k⟩ => (do (pure true) : RustM Bool))
            (fun ⟨acc, carry, k⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt k (5 : usize)) : RustM Bool))
            (fun ⟨acc, carry, k⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple3.mk acc carry k)
            (fun ⟨acc, carry, k⟩ =>
              (do
              let new_carry : u64 ← ((← acc[k]_?) >>>? (63 : i32));
              let acc : (RustArray u64 5) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  acc
                  k
                  (← (Rust_primitives.Hax.Machine_int.bitor
                    (← ((← acc[k]_?) <<<? (1 : i32)))
                    carry)));
              let carry : u64 := new_carry;
              let k : usize ← (k +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple3.mk acc carry k)) :
              RustM (Rust_primitives.Hax.Tuple3 (RustArray u64 5) u64 usize))));
        let word_idx : usize ←
          (Rust_primitives.Hax.cast_op (← (bit /? (64 : i32))));
        let bit_idx : u32 ←
          (Rust_primitives.Hax.cast_op (← (bit %? (64 : i32))));
        let b : u64 ←
          ((← ((← s_words[word_idx]_?) >>>? bit_idx)) &&&? (1 : u64));
        let acc : (RustArray u64 5) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            acc
            (0 : usize)
            (← (Core_models.Num.Impl_9.wrapping_add (← acc[(0 : usize)]_?) b)));
        let acc : (RustArray u64 5) ←
          if
          (← (Rust_primitives.Hax.Machine_int.lt (← acc[(0 : usize)]_?) b)) then
            let acc : (RustArray u64 5) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                acc
                (1 : usize)
                (← (Core_models.Num.Impl_9.wrapping_add
                  (← acc[(1 : usize)]_?)
                  (1 : u64))));
            (pure acc)
          else
            (pure acc);
        let acc : (RustArray u64 5) ←
          if (← (ge_l acc l_words)) then
            let acc : (RustArray u64 5) ← (sub_l acc l_words);
            (pure acc)
          else
            (pure acc);
        let bit : i32 ← (bit -? (1 : i32));
        (pure (Rust_primitives.Hax.Tuple2.mk acc bit)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u64 5) i32))));
  let result : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun ⟨i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i result)
      (fun ⟨i, result⟩ =>
        (do
        let bytes : (RustArray u8 8) ←
          (Core_models.Num.Impl_9.to_le_bytes (← acc[i]_?));
        let j : usize := (0 : usize);
        let ⟨j, result⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, result⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, result⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (8 : usize)) : RustM Bool))
            (fun ⟨j, result⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j result)
            (fun ⟨j, result⟩ =>
              (do
              let result : (RustArray u8 32) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  result
                  (← ((← (i *? (8 : usize))) +? j))
                  (← bytes[j]_?));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j result)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i result)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
  (pure result)

--  Scalar addition mod L. Both inputs and output are 32-byte little-endian.
def scalar_add (a : (RustArray u8 32)) (b : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  let sum : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let carry : u16 := (0 : u16);
  let i : usize := (0 : usize);
  let ⟨carry, i, sum⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨carry, i, sum⟩ => (do (pure true) : RustM Bool))
      (fun ⟨carry, i, sum⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨carry, i, sum⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk carry i sum)
      (fun ⟨carry, i, sum⟩ =>
        (do
        let s : u16 ←
          ((← ((← (Rust_primitives.Hax.cast_op (← a[i]_?)))
              +? (← (Rust_primitives.Hax.cast_op (← b[i]_?)))))
            +? carry);
        let sum : (RustArray u8 64) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            sum
            i
            (← (Rust_primitives.Hax.cast_op s)));
        let carry : u16 ← (s >>>? (8 : i32));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple3.mk carry i sum)) :
        RustM (Rust_primitives.Hax.Tuple3 u16 usize (RustArray u8 64)))));
  let sum : (RustArray u8 64) ←
    if (← (Rust_primitives.Hax.Machine_int.gt carry (0 : u16))) then
      let sum : (RustArray u8 64) ←
        (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
          sum
          (32 : usize)
          (← (Rust_primitives.Hax.cast_op carry)));
      (pure sum)
    else
      (pure sum);
  (scalar_reduce sum)

--  Scalar multiplication mod L (schoolbook). Both inputs are 32-byte LE.
def scalar_mul_mod_l (a : (RustArray u8 32)) (b : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  let product : (RustArray u32 64) ←
    (Rust_primitives.Hax.repeat (0 : u32) (64 : usize));
  let i : usize := (0 : usize);
  let ⟨i, product⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, product⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, product⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, product⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i product)
      (fun ⟨i, product⟩ =>
        (do
        let j : usize := (0 : usize);
        let ⟨j, product⟩ ←
          (Rust_primitives.Hax.while_loop
            (fun ⟨j, product⟩ => (do (pure true) : RustM Bool))
            (fun ⟨j, product⟩ =>
              (do
              (Rust_primitives.Hax.Machine_int.lt j (32 : usize)) : RustM Bool))
            (fun ⟨j, product⟩ =>
              (do
              (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
              RustM Hax_lib.Int.Int))
            (Rust_primitives.Hax.Tuple2.mk j product)
            (fun ⟨j, product⟩ =>
              (do
              let product : (RustArray u32 64) ←
                (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                  product
                  (← (i +? j))
                  (← ((← product[(← (i +? j))]_?)
                    +? (← ((← (Rust_primitives.Hax.cast_op (← a[i]_?)))
                      *? (← (Rust_primitives.Hax.cast_op (← b[j]_?))))))));
              let j : usize ← (j +? (1 : usize));
              (pure (Rust_primitives.Hax.Tuple2.mk j product)) :
              RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u32 64)))));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i product)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u32 64)))));
  let result : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let carry : u32 := (0 : u32);
  let i : usize := (0 : usize);
  let ⟨carry, i, result⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨carry, i, result⟩ => (do (pure true) : RustM Bool))
      (fun ⟨carry, i, result⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (64 : usize)) : RustM Bool))
      (fun ⟨carry, i, result⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk carry i result)
      (fun ⟨carry, i, result⟩ =>
        (do
        let s : u32 ← ((← product[i]_?) +? carry);
        let result : (RustArray u8 64) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            result
            i
            (← (Rust_primitives.Hax.cast_op s)));
        let carry : u32 ← (s >>>? (8 : i32));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple3.mk carry i result)) :
        RustM (Rust_primitives.Hax.Tuple3 u32 usize (RustArray u8 64)))));
  (scalar_reduce result)

end Libcrux_specs_hax.Edwards25519


namespace Libcrux_specs_hax.Ed25519

--  Clamp a 32-byte hash prefix into a valid Ed25519 scalar.
-- 
--  Per RFC 8032: clear the lowest 3 bits, clear bit 255, set bit 254.
def clamp (h : (RustArray u8 32)) : RustM (RustArray u8 32) := do
  let a : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨a, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨a, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨a, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨a, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk a i)
      (fun ⟨a, i⟩ =>
        (do
        let a : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            a
            i
            (← h[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk a i)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 32) usize))));
  let a : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      a
      (0 : usize)
      (← ((← a[(0 : usize)]_?) &&&? (248 : u8))));
  let a : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      a
      (31 : usize)
      (← ((← a[(31 : usize)]_?) &&&? (127 : u8))));
  let a : (RustArray u8 32) ←
    (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
      a
      (31 : usize)
      (← (Rust_primitives.Hax.Machine_int.bitor
        (← a[(31 : usize)]_?)
        (64 : u8))));
  (pure a)

--  Derive the Ed25519 public key from a 32-byte secret key.
-- 
--  1. Compute h = SHA-512(secret_key).
--  2. Clamp h[0..32] to get scalar a.
--  3. Return encode(a * B).
def ed25519_public_key (secret_key : (RustArray u8 32)) :
    RustM (RustArray u8 32) := do
  let h : (RustArray u8 64) ←
    (Libcrux_specs_hax.Sha512.sha512 (← (Rust_primitives.unsize secret_key)));
  let h_lo : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨h_lo, i⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨h_lo, i⟩ => (do (pure true) : RustM Bool))
      (fun ⟨h_lo, i⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨h_lo, i⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk h_lo i)
      (fun ⟨h_lo, i⟩ =>
        (do
        let h_lo : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            h_lo
            i
            (← h[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk h_lo i)) :
        RustM (Rust_primitives.Hax.Tuple2 (RustArray u8 32) usize))));
  let a : (RustArray u8 32) ← (clamp h_lo);
  let base : Libcrux_specs_hax.Edwards25519.EdPoint ←
    (Libcrux_specs_hax.Edwards25519.ed25519_base_point
      Rust_primitives.Hax.Tuple0.mk);
  let public_point : Libcrux_specs_hax.Edwards25519.EdPoint ←
    (Libcrux_specs_hax.Edwards25519.scalar_mult a base);
  (Libcrux_specs_hax.Edwards25519.point_encode public_point)

--  Ed25519 signature generation (RFC 8032, Section 5.1.6).
-- 
--  Input: 32-byte secret key, arbitrary-length message.
--  Output: 64-byte signature (R_enc || S_enc).
-- 
--  Steps:
--  1. h = SHA-512(secret_key)
--  2. a = clamp(h[0..32])
--  3. prefix = h[32..64]
--  4. r = SHA-512(prefix || msg) mod L
--  5. R = r * B
--  6. public_key = encode(a * B)
--  7. k = SHA-512(R_enc || public_key || msg) mod L
--  8. S = (r + k * a) mod L
--  9. Return R_enc || S_enc
def ed25519_sign (secret_key : (RustArray u8 32)) (msg : (RustSlice u8)) :
    RustM (RustArray u8 64) := do
  let h : (RustArray u8 64) ←
    (Libcrux_specs_hax.Sha512.sha512 (← (Rust_primitives.unsize secret_key)));
  let h_lo : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let prefix : (RustArray u8 32) ←
    (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
  let i : usize := (0 : usize);
  let ⟨h_lo, i, prefix⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨h_lo, i, prefix⟩ => (do (pure true) : RustM Bool))
      (fun ⟨h_lo, i, prefix⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨h_lo, i, prefix⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple3.mk h_lo i prefix)
      (fun ⟨h_lo, i, prefix⟩ =>
        (do
        let h_lo : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            h_lo
            i
            (← h[i]_?));
        let prefix : (RustArray u8 32) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            prefix
            i
            (← h[(← ((32 : usize) +? i))]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple3.mk h_lo i prefix)) :
        RustM
        (Rust_primitives.Hax.Tuple3
          (RustArray u8 32)
          usize
          (RustArray u8 32)))));
  let a : (RustArray u8 32) ← (clamp h_lo);
  let base : Libcrux_specs_hax.Edwards25519.EdPoint ←
    (Libcrux_specs_hax.Edwards25519.ed25519_base_point
      Rust_primitives.Hax.Tuple0.mk);
  let public_point : Libcrux_specs_hax.Edwards25519.EdPoint ←
    (Libcrux_specs_hax.Edwards25519.scalar_mult a base);
  let public_key : (RustArray u8 32) ←
    (Libcrux_specs_hax.Edwards25519.point_encode public_point);
  let r_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let i : usize := (0 : usize);
  let ⟨i, r_input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, r_input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, r_input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, r_input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i r_input)
      (fun ⟨i, r_input⟩ =>
        (do
        let r_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global r_input (← prefix[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i r_input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let i : usize := (0 : usize);
  let ⟨i, r_input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, r_input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, r_input⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt
          i
          (← (Core_models.Slice.Impl.len u8 msg))) :
        RustM Bool))
      (fun ⟨i, r_input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i r_input)
      (fun ⟨i, r_input⟩ =>
        (do
        let r_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global r_input (← msg[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i r_input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let r_hash : (RustArray u8 64) ←
    (Libcrux_specs_hax.Sha512.sha512
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) r_input)));
  let r_scalar : (RustArray u8 32) ←
    (Libcrux_specs_hax.Edwards25519.scalar_reduce r_hash);
  let r_point : Libcrux_specs_hax.Edwards25519.EdPoint ←
    (Libcrux_specs_hax.Edwards25519.scalar_mult r_scalar base);
  let r_enc : (RustArray u8 32) ←
    (Libcrux_specs_hax.Edwards25519.point_encode r_point);
  let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
    (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
  let i : usize := (0 : usize);
  let ⟨i, k_input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, k_input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, k_input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, k_input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i k_input)
      (fun ⟨i, k_input⟩ =>
        (do
        let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global k_input (← r_enc[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i k_input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let i : usize := (0 : usize);
  let ⟨i, k_input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, k_input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, k_input⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, k_input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i k_input)
      (fun ⟨i, k_input⟩ =>
        (do
        let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
            k_input
            (← public_key[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i k_input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let i : usize := (0 : usize);
  let ⟨i, k_input⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, k_input⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, k_input⟩ =>
        (do
        (Rust_primitives.Hax.Machine_int.lt
          i
          (← (Core_models.Slice.Impl.len u8 msg))) :
        RustM Bool))
      (fun ⟨i, k_input⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i k_input)
      (fun ⟨i, k_input⟩ =>
        (do
        let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
          (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global k_input (← msg[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i k_input)) :
        RustM
        (Rust_primitives.Hax.Tuple2
          usize
          (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
  let k_hash : (RustArray u8 64) ←
    (Libcrux_specs_hax.Sha512.sha512
      (← (Core_models.Ops.Deref.Deref.deref
        (Alloc.Vec.Vec u8 Alloc.Alloc.Global) k_input)));
  let k_scalar : (RustArray u8 32) ←
    (Libcrux_specs_hax.Edwards25519.scalar_reduce k_hash);
  let ka : (RustArray u8 32) ←
    (Libcrux_specs_hax.Edwards25519.scalar_mul_mod_l k_scalar a);
  let s : (RustArray u8 32) ←
    (Libcrux_specs_hax.Edwards25519.scalar_add r_scalar ka);
  let signature : (RustArray u8 64) ←
    (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
  let i : usize := (0 : usize);
  let ⟨i, signature⟩ ←
    (Rust_primitives.Hax.while_loop
      (fun ⟨i, signature⟩ => (do (pure true) : RustM Bool))
      (fun ⟨i, signature⟩ =>
        (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
      (fun ⟨i, signature⟩ =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      (Rust_primitives.Hax.Tuple2.mk i signature)
      (fun ⟨i, signature⟩ =>
        (do
        let signature : (RustArray u8 64) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            signature
            i
            (← r_enc[i]_?));
        let signature : (RustArray u8 64) ←
          (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
            signature
            (← ((32 : usize) +? i))
            (← s[i]_?));
        let i : usize ← (i +? (1 : usize));
        (pure (Rust_primitives.Hax.Tuple2.mk i signature)) :
        RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 64)))));
  (pure signature)

--  Ed25519 signature verification (RFC 8032, Section 5.1.7).
-- 
--  Input: 32-byte public key, arbitrary-length message, 64-byte signature.
--  Output: true if the signature is valid.
-- 
--  Steps:
--  1. A = decode(public_key)
--  2. R = decode(signature[0..32])
--  3. S = le_decode(signature[32..64])
--  4. k = SHA-512(R_enc || public_key || msg) mod L
--  5. Check: S * B == R + k * A
def ed25519_verify
    (public_key : (RustArray u8 32))
    (msg : (RustSlice u8))
    (signature : (RustArray u8 64)) :
    RustM Bool := do
  match (← (Libcrux_specs_hax.Edwards25519.point_decode public_key)) with
    | (Core_models.Option.Option.Some  p) =>
      let a_point : Libcrux_specs_hax.Edwards25519.EdPoint := p;
      let r_enc : (RustArray u8 32) ←
        (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
      let i : usize := (0 : usize);
      let ⟨i, r_enc⟩ ←
        (Rust_primitives.Hax.while_loop
          (fun ⟨i, r_enc⟩ => (do (pure true) : RustM Bool))
          (fun ⟨i, r_enc⟩ =>
            (do
            (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
          (fun ⟨i, r_enc⟩ =>
            (do
            (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
            RustM Hax_lib.Int.Int))
          (Rust_primitives.Hax.Tuple2.mk i r_enc)
          (fun ⟨i, r_enc⟩ =>
            (do
            let r_enc : (RustArray u8 32) ←
              (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                r_enc
                i
                (← signature[i]_?));
            let i : usize ← (i +? (1 : usize));
            (pure (Rust_primitives.Hax.Tuple2.mk i r_enc)) :
            RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
      match (← (Libcrux_specs_hax.Edwards25519.point_decode r_enc)) with
        | (Core_models.Option.Option.Some  p) =>
          let r_point : Libcrux_specs_hax.Edwards25519.EdPoint := p;
          let s_bytes : (RustArray u8 32) ←
            (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
          let i : usize := (0 : usize);
          let ⟨i, s_bytes⟩ ←
            (Rust_primitives.Hax.while_loop
              (fun ⟨i, s_bytes⟩ => (do (pure true) : RustM Bool))
              (fun ⟨i, s_bytes⟩ =>
                (do
                (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) :
                RustM Bool))
              (fun ⟨i, s_bytes⟩ =>
                (do
                (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                RustM Hax_lib.Int.Int))
              (Rust_primitives.Hax.Tuple2.mk i s_bytes)
              (fun ⟨i, s_bytes⟩ =>
                (do
                let s_bytes : (RustArray u8 32) ←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    s_bytes
                    i
                    (← signature[(← ((32 : usize) +? i))]_?));
                let i : usize ← (i +? (1 : usize));
                (pure (Rust_primitives.Hax.Tuple2.mk i s_bytes)) :
                RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 32)))));
          let l_bytes : (RustArray u8 32) :=
            #v[(237 : u8),
                 (211 : u8),
                 (245 : u8),
                 (92 : u8),
                 (26 : u8),
                 (99 : u8),
                 (18 : u8),
                 (88 : u8),
                 (214 : u8),
                 (156 : u8),
                 (247 : u8),
                 (162 : u8),
                 (222 : u8),
                 (249 : u8),
                 (222 : u8),
                 (20 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (0 : u8),
                 (16 : u8)];
          let s_ge_l : Bool := false;
          let i : usize := (32 : usize);
          let ⟨i, s_ge_l⟩ ←
            (Rust_primitives.Hax.while_loop_cf
              (fun ⟨i, s_ge_l⟩ => (do (pure true) : RustM Bool))
              (fun ⟨i, s_ge_l⟩ =>
                (do
                (Rust_primitives.Hax.Machine_int.gt i (0 : usize)) :
                RustM Bool))
              (fun ⟨i, s_ge_l⟩ =>
                (do
                (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                RustM Hax_lib.Int.Int))
              (Rust_primitives.Hax.Tuple2.mk i s_ge_l)
              (fun ⟨i, s_ge_l⟩ =>
                (do
                let i : usize ← (i -? (1 : usize));
                if
                (← (Rust_primitives.Hax.Machine_int.gt
                  (← s_bytes[i]_?)
                  (← l_bytes[i]_?))) then
                  let s_ge_l : Bool := true;
                  (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                    (Rust_primitives.Hax.Tuple2.mk
                      Rust_primitives.Hax.Tuple0.mk
                      (Rust_primitives.Hax.Tuple2.mk i s_ge_l))))
                else
                  if
                  (← (Rust_primitives.Hax.Machine_int.lt
                    (← s_bytes[i]_?)
                    (← l_bytes[i]_?))) then
                    (pure (Core_models.Ops.Control_flow.ControlFlow.Break
                      (Rust_primitives.Hax.Tuple2.mk
                        Rust_primitives.Hax.Tuple0.mk
                        (Rust_primitives.Hax.Tuple2.mk i s_ge_l))))
                  else
                    (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
                      (Rust_primitives.Hax.Tuple2.mk i s_ge_l))) :
                RustM
                (Core_models.Ops.Control_flow.ControlFlow
                  (Rust_primitives.Hax.Tuple2
                    Rust_primitives.Hax.Tuple0
                    (Rust_primitives.Hax.Tuple2 usize Bool))
                  (Rust_primitives.Hax.Tuple2 usize Bool)))));
          if s_ge_l then
            (pure false)
          else
            let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
              (Alloc.Vec.Impl.new u8 Rust_primitives.Hax.Tuple0.mk);
            let i : usize := (0 : usize);
            let ⟨i, k_input⟩ ←
              (Rust_primitives.Hax.while_loop
                (fun ⟨i, k_input⟩ => (do (pure true) : RustM Bool))
                (fun ⟨i, k_input⟩ =>
                  (do
                  (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) :
                  RustM Bool))
                (fun ⟨i, k_input⟩ =>
                  (do
                  (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                  RustM Hax_lib.Int.Int))
                (Rust_primitives.Hax.Tuple2.mk i k_input)
                (fun ⟨i, k_input⟩ =>
                  (do
                  let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                      k_input
                      (← r_enc[i]_?));
                  let i : usize ← (i +? (1 : usize));
                  (pure (Rust_primitives.Hax.Tuple2.mk i k_input)) :
                  RustM
                  (Rust_primitives.Hax.Tuple2
                    usize
                    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
            let i : usize := (0 : usize);
            let ⟨i, k_input⟩ ←
              (Rust_primitives.Hax.while_loop
                (fun ⟨i, k_input⟩ => (do (pure true) : RustM Bool))
                (fun ⟨i, k_input⟩ =>
                  (do
                  (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) :
                  RustM Bool))
                (fun ⟨i, k_input⟩ =>
                  (do
                  (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                  RustM Hax_lib.Int.Int))
                (Rust_primitives.Hax.Tuple2.mk i k_input)
                (fun ⟨i, k_input⟩ =>
                  (do
                  let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                      k_input
                      (← public_key[i]_?));
                  let i : usize ← (i +? (1 : usize));
                  (pure (Rust_primitives.Hax.Tuple2.mk i k_input)) :
                  RustM
                  (Rust_primitives.Hax.Tuple2
                    usize
                    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
            let i : usize := (0 : usize);
            let ⟨i, k_input⟩ ←
              (Rust_primitives.Hax.while_loop
                (fun ⟨i, k_input⟩ => (do (pure true) : RustM Bool))
                (fun ⟨i, k_input⟩ =>
                  (do
                  (Rust_primitives.Hax.Machine_int.lt
                    i
                    (← (Core_models.Slice.Impl.len u8 msg))) :
                  RustM Bool))
                (fun ⟨i, k_input⟩ =>
                  (do
                  (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                  RustM Hax_lib.Int.Int))
                (Rust_primitives.Hax.Tuple2.mk i k_input)
                (fun ⟨i, k_input⟩ =>
                  (do
                  let k_input : (Alloc.Vec.Vec u8 Alloc.Alloc.Global) ←
                    (Alloc.Vec.Impl_1.push u8 Alloc.Alloc.Global
                      k_input
                      (← msg[i]_?));
                  let i : usize ← (i +? (1 : usize));
                  (pure (Rust_primitives.Hax.Tuple2.mk i k_input)) :
                  RustM
                  (Rust_primitives.Hax.Tuple2
                    usize
                    (Alloc.Vec.Vec u8 Alloc.Alloc.Global)))));
            let k_hash : (RustArray u8 64) ←
              (Libcrux_specs_hax.Sha512.sha512
                (← (Core_models.Ops.Deref.Deref.deref
                  (Alloc.Vec.Vec u8 Alloc.Alloc.Global) k_input)));
            let k_scalar : (RustArray u8 32) ←
              (Libcrux_specs_hax.Edwards25519.scalar_reduce k_hash);
            let base : Libcrux_specs_hax.Edwards25519.EdPoint ←
              (Libcrux_specs_hax.Edwards25519.ed25519_base_point
                Rust_primitives.Hax.Tuple0.mk);
            let sb : Libcrux_specs_hax.Edwards25519.EdPoint ←
              (Libcrux_specs_hax.Edwards25519.scalar_mult s_bytes base);
            let ka : Libcrux_specs_hax.Edwards25519.EdPoint ←
              (Libcrux_specs_hax.Edwards25519.scalar_mult k_scalar a_point);
            let rka : Libcrux_specs_hax.Edwards25519.EdPoint ←
              (Libcrux_specs_hax.Edwards25519.point_add r_point ka);
            let sb_enc : (RustArray u8 32) ←
              (Libcrux_specs_hax.Edwards25519.point_encode sb);
            let rka_enc : (RustArray u8 32) ←
              (Libcrux_specs_hax.Edwards25519.point_encode rka);
            (Core_models.Cmp.PartialEq.eq
              (RustArray u8 32)
              (RustArray u8 32) sb_enc rka_enc)
        | (Core_models.Option.Option.None ) => (pure false)
    | (Core_models.Option.Option.None ) => (pure false)

end Libcrux_specs_hax.Ed25519


namespace Libcrux_specs_hax.Ecdsa_p256

--  Check if a scalar (mod n) is zero.
def is_zero (a : (RustArray u64 4)) : RustM Bool := do
  ((← ((← ((← (Rust_primitives.Hax.Machine_int.eq
          (← a[(0 : usize)]_?)
          (0 : u64)))
        &&? (← (Rust_primitives.Hax.Machine_int.eq
          (← a[(1 : usize)]_?)
          (0 : u64)))))
      &&? (← (Rust_primitives.Hax.Machine_int.eq
        (← a[(2 : usize)]_?)
        (0 : u64)))))
    &&? (← (Rust_primitives.Hax.Machine_int.eq (← a[(3 : usize)]_?) (0 : u64))))

--  Compare two 256-bit big-endian numbers. Returns true if a >= b.
def ge256 (a : (RustArray u64 4)) (b : (RustArray u64 4)) : RustM Bool := do
  let i : usize := (0 : usize);
  match
    (← (Rust_primitives.Hax.while_loop_return
      (fun i => (do (pure true) : RustM Bool))
      (fun i =>
        (do (Rust_primitives.Hax.Machine_int.lt i (4 : usize)) : RustM Bool))
      (fun i =>
        (do
        (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
        RustM Hax_lib.Int.Int))
      i
      (fun i =>
        (do
        if (← (Rust_primitives.Hax.Machine_int.gt (← a[i]_?) (← b[i]_?))) then
          (pure (Core_models.Ops.Control_flow.ControlFlow.Break
            (Core_models.Ops.Control_flow.ControlFlow.Break true)))
        else
          if (← (Rust_primitives.Hax.Machine_int.lt (← a[i]_?) (← b[i]_?))) then
            (pure (Core_models.Ops.Control_flow.ControlFlow.Break
              (Core_models.Ops.Control_flow.ControlFlow.Break false)))
          else
            (pure (Core_models.Ops.Control_flow.ControlFlow.Continue
              (← (i +? (1 : usize))))) :
        RustM
        (Core_models.Ops.Control_flow.ControlFlow
          (Core_models.Ops.Control_flow.ControlFlow
            Bool
            (Rust_primitives.Hax.Tuple2 Rust_primitives.Hax.Tuple0 usize))
          usize)))))
  with
    | (Core_models.Ops.Control_flow.ControlFlow.Break  ret) => (pure ret)
    | (Core_models.Ops.Control_flow.ControlFlow.Continue  i) => (pure true)

--  Reduce a field element mod n (the curve order).
--  If a >= n, subtract n.
def reduce_mod_n (a : (RustArray u64 4)) : RustM (RustArray u64 4) := do
  if (← (ge256 a Libcrux_specs_hax.P256.P256_N)) then
    let r : (RustArray u64 4) ←
      (Rust_primitives.Hax.repeat (0 : u64) (4 : usize));
    let borrow : u128 := (0 : u128);
    let i : usize := (4 : usize);
    let ⟨borrow, i, r⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨borrow, i, r⟩ => (do (pure true) : RustM Bool))
        (fun ⟨borrow, i, r⟩ =>
          (do (Rust_primitives.Hax.Machine_int.gt i (0 : usize)) : RustM Bool))
        (fun ⟨borrow, i, r⟩ =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple3.mk borrow i r)
        (fun ⟨borrow, i, r⟩ =>
          (do
          let i : usize ← (i -? (1 : usize));
          let s : u128 ←
            (Core_models.Num.Impl_10.wrapping_sub
              (← (Core_models.Num.Impl_10.wrapping_sub
                (← (Rust_primitives.Hax.cast_op (← a[i]_?)))
                (← (Rust_primitives.Hax.cast_op
                  (← Libcrux_specs_hax.P256.P256_N[i]_?)))))
              borrow);
          let r : (RustArray u64 4) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              r
              i
              (← (Rust_primitives.Hax.cast_op s)));
          let borrow : u128 ← ((← (s >>>? (127 : i32))) &&&? (1 : u128));
          (pure (Rust_primitives.Hax.Tuple3.mk borrow i r)) :
          RustM (Rust_primitives.Hax.Tuple3 u128 usize (RustArray u64 4)))));
    (pure r)
  else
    (pure a)

--  ECDSA P-256 signature generation (FIPS 186-4, Section 6.4).
-- 
--  Input:
--  - `secret_key`: 32-byte big-endian private key d.
--  - `msg`: arbitrary-length message.
--  - `k_random`: 32-byte big-endian random nonce k (must be in [1, n-1]).
-- 
--  Output:
--  - `Some([u8; 64])` containing r || s (each 32 bytes, big-endian).
--  - `None` if r == 0 or s == 0.
-- 
--  Steps:
--  1. e = SHA-256(msg)
--  2. (x1, _) = k * G
--  3. r = x1 mod n (return None if r == 0)
--  4. s = k^(-1) * (e + r * d) mod n (return None if s == 0)
--  5. Return r || s
def ecdsa_p256_sign
    (secret_key : (RustArray u8 32))
    (msg : (RustSlice u8))
    (k_random : (RustArray u8 32)) :
    RustM (Core_models.Option.Option (RustArray u8 64)) := do
  let d : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_from_bytes secret_key);
  let k : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_from_bytes k_random);
  if (← (is_zero k)) then
    (pure Core_models.Option.Option.None)
  else
    let e_hash : (RustArray u8 32) ← (Libcrux_specs_hax.Sha256.sha256 msg);
    let e : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_from_bytes e_hash);
    let kg : Libcrux_specs_hax.P256.P256Point ←
      (Libcrux_specs_hax.P256.base_mult k_random);
    if (← (Libcrux_specs_hax.P256.point_is_identity kg)) then
      (pure Core_models.Option.Option.None)
    else
      let x1 : (RustArray u64 4) ← (Libcrux_specs_hax.P256.point_affine_x kg);
      let r : (RustArray u64 4) ← (reduce_mod_n x1);
      if (← (is_zero r)) then
        (pure Core_models.Option.Option.None)
      else
        let k_inv : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_inv k);
        let rd : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_mul r d);
        let e_rd : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_add e rd);
        let s : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_mul k_inv e_rd);
        if (← (is_zero s)) then
          (pure Core_models.Option.Option.None)
        else
          let sig : (RustArray u8 64) ←
            (Rust_primitives.Hax.repeat (0 : u8) (64 : usize));
          let r_bytes : (RustArray u8 32) ←
            (Libcrux_specs_hax.P256.fp_to_bytes r);
          let s_bytes : (RustArray u8 32) ←
            (Libcrux_specs_hax.P256.fp_to_bytes s);
          let i : usize := (0 : usize);
          let ⟨i, sig⟩ ←
            (Rust_primitives.Hax.while_loop
              (fun ⟨i, sig⟩ => (do (pure true) : RustM Bool))
              (fun ⟨i, sig⟩ =>
                (do
                (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) :
                RustM Bool))
              (fun ⟨i, sig⟩ =>
                (do
                (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
                RustM Hax_lib.Int.Int))
              (Rust_primitives.Hax.Tuple2.mk i sig)
              (fun ⟨i, sig⟩ =>
                (do
                let sig : (RustArray u8 64) ←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    sig
                    i
                    (← r_bytes[i]_?));
                let sig : (RustArray u8 64) ←
                  (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
                    sig
                    (← ((32 : usize) +? i))
                    (← s_bytes[i]_?));
                let i : usize ← (i +? (1 : usize));
                (pure (Rust_primitives.Hax.Tuple2.mk i sig)) :
                RustM (Rust_primitives.Hax.Tuple2 usize (RustArray u8 64)))));
          (pure (Core_models.Option.Option.Some sig))

--  ECDSA P-256 signature verification (FIPS 186-4, Section 6.4).
-- 
--  Input:
--  - `public_key`: 65-byte uncompressed public key (0x04 || x || y).
--  - `msg`: arbitrary-length message.
--  - `signature`: 64-byte signature (r || s, each 32 bytes big-endian).
-- 
--  Output: true if the signature is valid.
-- 
--  Steps:
--  1. e = SHA-256(msg) as integer mod n
--  2. r, s = decode signature
--  3. Check 1 <= r, s < n
--  4. w = s^(-1) mod n
--  5. u1 = e * w mod n, u2 = r * w mod n
--  6. (x1, _) = u1 * G + u2 * Q
--  7. Check x1 mod n == r
def ecdsa_p256_verify
    (public_key : (RustArray u8 65))
    (msg : (RustSlice u8))
    (signature : (RustArray u8 64)) :
    RustM Bool := do
  if
  (← (Rust_primitives.Hax.Machine_int.ne
    (← public_key[(0 : usize)]_?)
    (4 : u8))) then
    (pure false)
  else
    let qx_bytes : (RustArray u8 32) ←
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    let qy_bytes : (RustArray u8 32) ←
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    let i : usize := (0 : usize);
    let ⟨i, qx_bytes, qy_bytes⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨i, qx_bytes, qy_bytes⟩ => (do (pure true) : RustM Bool))
        (fun ⟨i, qx_bytes, qy_bytes⟩ =>
          (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
        (fun ⟨i, qx_bytes, qy_bytes⟩ =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple3.mk i qx_bytes qy_bytes)
        (fun ⟨i, qx_bytes, qy_bytes⟩ =>
          (do
          let qx_bytes : (RustArray u8 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              qx_bytes
              i
              (← public_key[(← ((1 : usize) +? i))]_?));
          let qy_bytes : (RustArray u8 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              qy_bytes
              i
              (← public_key[(← ((33 : usize) +? i))]_?));
          let i : usize ← (i +? (1 : usize));
          (pure (Rust_primitives.Hax.Tuple3.mk i qx_bytes qy_bytes)) :
          RustM
          (Rust_primitives.Hax.Tuple3
            usize
            (RustArray u8 32)
            (RustArray u8 32)))));
    let qx : (RustArray u64 4) ←
      (Libcrux_specs_hax.P256.fp_from_bytes qx_bytes);
    let qy : (RustArray u64 4) ←
      (Libcrux_specs_hax.P256.fp_from_bytes qy_bytes);
    let q : Libcrux_specs_hax.P256.P256Point :=
      (Libcrux_specs_hax.P256.P256Point.mk
        (x := qx)
        (y := qy)
        (z := #v[(0 : u64), (0 : u64), (0 : u64), (1 : u64)]));
    let r_bytes : (RustArray u8 32) ←
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    let s_bytes : (RustArray u8 32) ←
      (Rust_primitives.Hax.repeat (0 : u8) (32 : usize));
    let i : usize := (0 : usize);
    let ⟨i, r_bytes, s_bytes⟩ ←
      (Rust_primitives.Hax.while_loop
        (fun ⟨i, r_bytes, s_bytes⟩ => (do (pure true) : RustM Bool))
        (fun ⟨i, r_bytes, s_bytes⟩ =>
          (do (Rust_primitives.Hax.Machine_int.lt i (32 : usize)) : RustM Bool))
        (fun ⟨i, r_bytes, s_bytes⟩ =>
          (do
          (Rust_primitives.Hax.Int.from_machine (0 : u32)) :
          RustM Hax_lib.Int.Int))
        (Rust_primitives.Hax.Tuple3.mk i r_bytes s_bytes)
        (fun ⟨i, r_bytes, s_bytes⟩ =>
          (do
          let r_bytes : (RustArray u8 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              r_bytes
              i
              (← signature[i]_?));
          let s_bytes : (RustArray u8 32) ←
            (Rust_primitives.Hax.Monomorphized_update_at.update_at_usize
              s_bytes
              i
              (← signature[(← ((32 : usize) +? i))]_?));
          let i : usize ← (i +? (1 : usize));
          (pure (Rust_primitives.Hax.Tuple3.mk i r_bytes s_bytes)) :
          RustM
          (Rust_primitives.Hax.Tuple3
            usize
            (RustArray u8 32)
            (RustArray u8 32)))));
    let r : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fp_from_bytes r_bytes);
    let s : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fp_from_bytes s_bytes);
    if (← ((← (is_zero r)) ||? (← (is_zero s)))) then
      (pure false)
    else
      if (← (ge256 r Libcrux_specs_hax.P256.P256_N)) then
        (pure false)
      else
        if (← (ge256 s Libcrux_specs_hax.P256.P256_N)) then
          (pure false)
        else
          let e_hash : (RustArray u8 32) ←
            (Libcrux_specs_hax.Sha256.sha256 msg);
          let e : (RustArray u64 4) ←
            (Libcrux_specs_hax.P256.fn_from_bytes e_hash);
          let w : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_inv s);
          let u1 : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_mul e w);
          let u2 : (RustArray u64 4) ← (Libcrux_specs_hax.P256.fn_mul r w);
          let u1_bytes : (RustArray u8 32) ←
            (Libcrux_specs_hax.P256.fp_to_bytes u1);
          let u2_bytes : (RustArray u8 32) ←
            (Libcrux_specs_hax.P256.fp_to_bytes u2);
          let u1g : Libcrux_specs_hax.P256.P256Point ←
            (Libcrux_specs_hax.P256.base_mult u1_bytes);
          let u2q : Libcrux_specs_hax.P256.P256Point ←
            (Libcrux_specs_hax.P256.scalar_mult u2_bytes q);
          let point : Libcrux_specs_hax.P256.P256Point ←
            (Libcrux_specs_hax.P256.point_add u1g u2q);
          if (← (Libcrux_specs_hax.P256.point_is_identity point)) then
            (pure false)
          else
            let x1 : (RustArray u64 4) ←
              (Libcrux_specs_hax.P256.point_affine_x point);
            let x1_mod_n : (RustArray u64 4) ← (reduce_mod_n x1);
            (Core_models.Cmp.PartialEq.eq
              (RustArray u64 4)
              (RustArray u64 4) x1_mod_n r)

--  Derive the ECDSA P-256 public key from a secret key.
-- 
--  Returns the 65-byte uncompressed encoding (0x04 || x || y).
def ecdsa_p256_public_key (secret_key : (RustArray u8 32)) :
    RustM (RustArray u8 65) := do
  let pk_point : Libcrux_specs_hax.P256.P256Point ←
    (Libcrux_specs_hax.P256.base_mult secret_key);
  (Libcrux_specs_hax.P256.point_to_uncompressed pk_point)

end Libcrux_specs_hax.Ecdsa_p256


namespace Libcrux_specs_hax

--  Fixed-length wrappers for the Lean extraction bridge.
--  These match the opaque declarations in Libcrux_specs.lean.
class LibcruxCrypto.AssociatedTypes (Self : Type) where

class LibcruxCrypto (Self : Type)
  [associatedTypes : outParam (LibcruxCrypto.AssociatedTypes (Self : Type))]
  where
  sha256_32 (Self) : ((RustArray u8 32) -> RustM (RustArray u8 32))
  hmac_sha256_32 (Self) :
    ((RustArray u8 32) -> (RustArray u8 32) -> RustM (RustArray u8 32))
  hkdf_extract_32 (Self) :
    ((RustArray u8 32) -> (RustArray u8 32) -> RustM (RustArray u8 32))
  hkdf_expand_32 (Self) :
    ((RustArray u8 32) -> (RustArray u8 32) -> RustM (RustArray u8 32))
  aes128_encrypt (Self) :
    ((RustArray u8 16) -> (RustArray u8 16) -> RustM (RustArray u8 16))
  x25519_scalarmult (Self) :
    ((RustArray u8 32) -> (RustArray u8 32) -> RustM (RustArray u8 32))
  x25519_base (Self) : ((RustArray u8 32) -> RustM (RustArray u8 32))
  ed25519_sign (Self) :
    ((RustArray u8 32) -> (RustSlice u8) -> RustM (RustArray u8 64))
  ed25519_verify (Self) :
    ((RustArray u8 32) -> (RustSlice u8) -> (RustArray u8 64) -> RustM Bool)

--  Concrete instantiation using the pure specs in this crate.
structure ConcreteLibcrux where
  -- no fields

@[reducible] instance Impl.AssociatedTypes :
  LibcruxCrypto.AssociatedTypes ConcreteLibcrux
  where

instance Impl : LibcruxCrypto ConcreteLibcrux where
  sha256_32 := fun (msg : (RustArray u8 32)) => do
    (Libcrux_specs_hax.Sha256.sha256_32 msg)
  hmac_sha256_32 :=
    fun (key : (RustArray u8 32)) (msg : (RustArray u8 32)) => do
    (Libcrux_specs_hax.Hmac.hmac_sha256_32 key msg)
  hkdf_extract_32 :=
    fun (salt : (RustArray u8 32)) (ikm : (RustArray u8 32)) => do
    (Libcrux_specs_hax.Hkdf.hkdf_extract_32 salt ikm)
  hkdf_expand_32 :=
    fun (prk : (RustArray u8 32)) (info : (RustArray u8 32)) => do
    (Libcrux_specs_hax.Hkdf.hkdf_expand_32 prk info)
  aes128_encrypt :=
    fun (key : (RustArray u8 16)) (block : (RustArray u8 16)) => do
    (Libcrux_specs_hax.Aes128.aes128_encrypt key block)
  x25519_scalarmult :=
    fun (scalar : (RustArray u8 32)) (point : (RustArray u8 32)) => do
    (Libcrux_specs_hax.X25519.scalarmult scalar point)
  x25519_base := fun (scalar : (RustArray u8 32)) => do
    (Libcrux_specs_hax.X25519.base_mult scalar)
  ed25519_sign :=
    fun (secret_key : (RustArray u8 32)) (msg : (RustSlice u8)) => do
    (Libcrux_specs_hax.Ed25519.ed25519_sign secret_key msg)
  ed25519_verify :=
    fun
      (public_key : (RustArray u8 32))
      (msg : (RustSlice u8))
      (signature : (RustArray u8 64)) => do
    (Libcrux_specs_hax.Ed25519.ed25519_verify public_key msg signature)

--  Convenience: SHA-512 on a 64-byte input (for Ed25519 internal use).
def sha512_64 (msg : (RustArray u8 64)) : RustM (RustArray u8 64) := do
  (Libcrux_specs_hax.Sha512.sha512 (← (Rust_primitives.unsize msg)))

end Libcrux_specs_hax

