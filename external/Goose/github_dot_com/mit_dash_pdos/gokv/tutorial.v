(* autogenerated from github.com/mit-pdos/gokv/tutorial *)
From Perennial.goose_lang Require Import prelude.
From Goose Require github_dot_com.mit_dash_pdos.gokv.grove__ffi.
From Goose Require github_dot_com.mit_dash_pdos.gokv.urpc.
From Goose Require github_dot_com.tchajed.goose.machine.
From Goose Require sync.

From Perennial.goose_lang Require Import ffi.grove_prelude.

Definition Decision: ty := byteT.

Definition Unknown : expr := #(U8 0).

Definition Commit : expr := #(U8 1).

Definition Abort : expr := #(U8 2).

Definition ParticipantServer := struct.decl [
  "m" :: ptrT;
  "preference" :: boolT
].

Definition ParticipantServer__GetPreference: val :=
  rec: "ParticipantServer__GetPreference" "s" :=
    let: "s" := ref_to ptrT "s" in
    sync.Mutex__Lock (struct.loadF ParticipantServer "m" (![ptrT] "s"));;
    let: "pref" := ref_zero boolT in
    let: "$a0" := struct.loadF ParticipantServer "preference" (![ptrT] "s") in
    "pref" <-[boolT] "$a0";;
    sync.Mutex__Unlock (struct.loadF ParticipantServer "m" (![ptrT] "s"));;
    return: (![boolT] "pref").

Definition MakeParticipant: val :=
  rec: "MakeParticipant" "pref" :=
    let: "pref" := ref_to boolT "pref" in
    return: (struct.new ParticipantServer [
       "m" ::= struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex));
       "preference" ::= ![boolT] "pref"
     ]).

Definition ParticipantClerk := struct.decl [
  "client" :: ptrT
].

Definition CoordinatorServer := struct.decl [
  "m" :: ptrT;
  "decision" :: byteT;
  "preferences" :: slice.T byteT;
  "participants" :: slice.T ptrT
].

Definition CoordinatorClerk := struct.decl [
  "client" :: ptrT
].

Definition Yes : expr := #true.

Definition No : expr := #false.

Definition GetPreferenceId : expr := #0.

Definition prefToByte: val :=
  rec: "prefToByte" "pref" :=
    let: "pref" := ref_to boolT "pref" in
    (if: ![boolT] "pref"
    then return: (#(U8 1))
    else return: (#(U8 0)));;
    #().

Definition byteToPref: val :=
  rec: "byteToPref" "b" :=
    let: "b" := ref_to byteT "b" in
    return: ((![byteT] "b") = #(U8 1)).

Definition ParticipantClerk__GetPreference: val :=
  rec: "ParticipantClerk__GetPreference" "ck" :=
    let: "ck" := ref_to ptrT "ck" in
    let: "req" := ref_zero (slice.T byteT) in
    let: "$a0" := NewSlice byteT #0 in
    "req" <-[slice.T byteT] "$a0";;
    let: "reply" := ref_to (slice.T byteT) (NewSlice byteT #0) in
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF ParticipantClerk "client" (![ptrT] "ck")) GetPreferenceId (![slice.T byteT] "req") "reply" #1000 in
    "err" <-[uint64T] "$a0";;
    machine.Assume ((![uint64T] "err") = #0);;
    let: "b" := ref_zero byteT in
    let: "$a0" := SliceGet byteT (![slice.T byteT] "reply") #0 in
    "b" <-[byteT] "$a0";;
    return: (byteToPref (![byteT] "b")).

(* make a decision once we have all the preferences

   assumes we have all preferences (ie, no Unknown) *)
Definition CoordinatorServer__makeDecision: val :=
  rec: "CoordinatorServer__makeDecision" "s" :=
    let: "s" := ref_to ptrT "s" in
    sync.Mutex__Lock (struct.loadF CoordinatorServer "m" (![ptrT] "s"));;
    ForSlice byteT <> "pref" (struct.loadF CoordinatorServer "preferences" (![ptrT] "s"))
      ((if: (![byteT] "pref") = Abort
      then
        let: "$a0" := Abort in
        struct.storeF CoordinatorServer "decision" (![ptrT] "s") "$a0";;
        #()
      else #());;
      #());;
    (if: (struct.loadF CoordinatorServer "decision" (![ptrT] "s")) = Unknown
    then
      let: "$a0" := Commit in
      struct.storeF CoordinatorServer "decision" (![ptrT] "s") "$a0";;
      #()
    else #());;
    sync.Mutex__Unlock (struct.loadF CoordinatorServer "m" (![ptrT] "s"));;
    #().

Definition prefToDecision: val :=
  rec: "prefToDecision" "pref" :=
    let: "pref" := ref_to boolT "pref" in
    (if: ![boolT] "pref"
    then return: (Commit)
    else return: (Abort));;
    #().

Definition CoordinatorServer__backgroundLoop: val :=
  rec: "CoordinatorServer__backgroundLoop" "s" :=
    let: "s" := ref_to ptrT "s" in
    ForSlice ptrT "i" "h" (struct.loadF CoordinatorServer "participants" (![ptrT] "s"))
      (let: "pref" := ref_zero boolT in
      let: "$a0" := ParticipantClerk__GetPreference (![ptrT] "h") in
      "pref" <-[boolT] "$a0";;
      sync.Mutex__Lock (struct.loadF CoordinatorServer "m" (![ptrT] "s"));;
      let: "$a0" := prefToDecision (![boolT] "pref") in
      SliceSet byteT (struct.loadF CoordinatorServer "preferences" (![ptrT] "s")) (![intT] "i") "$a0";;
      sync.Mutex__Unlock (struct.loadF CoordinatorServer "m" (![ptrT] "s"));;
      #());;
    CoordinatorServer__makeDecision (![ptrT] "s");;
    #().

Definition MakeCoordinator: val :=
  rec: "MakeCoordinator" "participants" :=
    let: "participants" := ref_to (slice.T uint64T) "participants" in
    let: "decision" := ref_zero byteT in
    let: "$a0" := Unknown in
    "decision" <-[byteT] "$a0";;
    let: "m" := ref_zero ptrT in
    let: "$a0" := struct.alloc sync.Mutex (zero_val (struct.t sync.Mutex)) in
    "m" <-[ptrT] "$a0";;
    let: "preferences" := ref_zero (slice.T byteT) in
    let: "$a0" := NewSlice byteT (slice.len (![slice.T uint64T] "participants")) in
    "preferences" <-[slice.T byteT] "$a0";;
    let: "clerks" := ref_to (slice.T ptrT) (NewSlice ptrT #0) in
    ForSlice uint64T <> "a" (![slice.T uint64T] "participants")
      (let: "client" := ref_zero ptrT in
      let: "$a0" := urpc.MakeClient (![uint64T] "a") in
      "client" <-[ptrT] "$a0";;
      let: "$a0" := SliceAppend ptrT (![slice.T ptrT] "clerks") (struct.new ParticipantClerk [
        "client" ::= ![ptrT] "client"
      ]) in
      "clerks" <-[slice.T ptrT] "$a0";;
      #());;
    return: (struct.new CoordinatorServer [
       "m" ::= ![ptrT] "m";
       "decision" ::= ![byteT] "decision";
       "preferences" ::= ![slice.T byteT] "preferences";
       "participants" ::= ![slice.T ptrT] "clerks"
     ]).

Definition GetDecisionId : expr := #1.

Definition CoordinatorClerk__GetDecision: val :=
  rec: "CoordinatorClerk__GetDecision" "ck" :=
    let: "ck" := ref_to ptrT "ck" in
    let: "req" := ref_zero (slice.T byteT) in
    let: "$a0" := NewSlice byteT #0 in
    "req" <-[slice.T byteT] "$a0";;
    let: "reply" := ref_to (slice.T byteT) (NewSlice byteT #1) in
    let: "err" := ref_zero uint64T in
    let: "$a0" := urpc.Client__Call (struct.loadF CoordinatorClerk "client" (![ptrT] "ck")) GetDecisionId (![slice.T byteT] "req") "reply" #1000 in
    "err" <-[uint64T] "$a0";;
    machine.Assume ((![uint64T] "err") = #0);;
    return: (SliceGet byteT (![slice.T byteT] "reply") #0).

Definition CoordinatorServer__GetDecision: val :=
  rec: "CoordinatorServer__GetDecision" "s" :=
    let: "s" := ref_to ptrT "s" in
    sync.Mutex__Lock (struct.loadF CoordinatorServer "m" (![ptrT] "s"));;
    let: "decision" := ref_zero byteT in
    let: "$a0" := struct.loadF CoordinatorServer "decision" (![ptrT] "s") in
    "decision" <-[byteT] "$a0";;
    sync.Mutex__Unlock (struct.loadF CoordinatorServer "m" (![ptrT] "s"));;
    return: (![byteT] "decision").

Definition CoordinatorMain: val :=
  rec: "CoordinatorMain" "me" "participants" :=
    let: "participants" := ref_to (slice.T uint64T) "participants" in
    let: "me" := ref_to uint64T "me" in
    let: "coordinator" := ref_zero ptrT in
    let: "$a0" := MakeCoordinator (![slice.T uint64T] "participants") in
    "coordinator" <-[ptrT] "$a0";;
    let: "handlers" := ref_zero (mapT (arrowT unitT unitT)) in
    let: "$a0" := NewMap uint64T (arrowT unitT unitT) #() in
    "handlers" <-[mapT (arrowT unitT unitT)] "$a0";;
    let: "$a0" := (λ: "_req" "reply",
      let: "decision" := ref_zero byteT in
      let: "$a0" := CoordinatorServer__GetDecision (![ptrT] "coordinator") in
      "decision" <-[byteT] "$a0";;
      let: "replyData" := ref_zero (slice.T byteT) in
      let: "$a0" := NewSlice byteT #1 in
      "replyData" <-[slice.T byteT] "$a0";;
      let: "$a0" := ![byteT] "decision" in
      SliceSet byteT (![slice.T byteT] "replyData") #0 "$a0";;
      let: "$a0" := ![slice.T byteT] "replyData" in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") GetDecisionId "$a0";;
    let: "server" := ref_zero ptrT in
    let: "$a0" := urpc.MakeServer (![mapT (arrowT unitT unitT)] "handlers") in
    "server" <-[ptrT] "$a0";;
    urpc.Server__Serve (![ptrT] "server") (![uint64T] "me");;
    Fork (CoordinatorServer__backgroundLoop (![ptrT] "coordinator");;
          #());;
    #().

Definition ParticipantMain: val :=
  rec: "ParticipantMain" "me" "pref" :=
    let: "pref" := ref_to boolT "pref" in
    let: "me" := ref_to uint64T "me" in
    let: "participant" := ref_zero ptrT in
    let: "$a0" := MakeParticipant (![boolT] "pref") in
    "participant" <-[ptrT] "$a0";;
    let: "handlers" := ref_zero (mapT (arrowT unitT unitT)) in
    let: "$a0" := NewMap uint64T (arrowT unitT unitT) #() in
    "handlers" <-[mapT (arrowT unitT unitT)] "$a0";;
    let: "$a0" := (λ: "_req" "reply",
      let: "pref" := ref_zero boolT in
      let: "$a0" := ParticipantServer__GetPreference (![ptrT] "participant") in
      "pref" <-[boolT] "$a0";;
      let: "replyData" := ref_zero (slice.T byteT) in
      let: "$a0" := NewSlice byteT #1 in
      "replyData" <-[slice.T byteT] "$a0";;
      let: "$a0" := prefToByte (![boolT] "pref") in
      SliceSet byteT (![slice.T byteT] "replyData") #0 "$a0";;
      let: "$a0" := ![slice.T byteT] "replyData" in
      (![ptrT] "reply") <-[slice.T byteT] "$a0";;
      #()
      ) in
    MapInsert (![mapT (arrowT unitT unitT)] "handlers") GetPreferenceId "$a0";;
    let: "server" := ref_zero ptrT in
    let: "$a0" := urpc.MakeServer (![mapT (arrowT unitT unitT)] "handlers") in
    "server" <-[ptrT] "$a0";;
    urpc.Server__Serve (![ptrT] "server") (![uint64T] "me");;
    #().
