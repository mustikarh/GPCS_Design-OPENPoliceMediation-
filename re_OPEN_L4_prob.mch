/* =====================================================================
 * re_OPEN_L4.mch  --  Scope A: OPEN Policy-Mediation (B classic / AMN)
 *
 * LEVEL 4 -- structural reformulation that REMOVES the recurring
 * "!aa-under-override" proof-obligation class (the POs that made `pp`
 * time out at every token_ok override), WITHOUT losing any requirement.
 *
 * KEY IDEA:
 *   token_ok is no longer a stored variable maintained by !aa-invariants.
 *   "Being trusted enough to install" is now a DERIVED predicate:
 *
 *     trusted(aa) == token_id(aa) /: deny_list
 *                    & ( req_mode(aa) = AUTHORIZED  or  aa : dm_verified )
 *
 *   where dm_verified <: pending records DELEGATED requests whose token
 *   has passed on-card verification.
 *
 *   Consequences:
 *     - OPN-21 (AUTHORIZED & not-deny-listed => trusted)  and
 *       OPN-11/20 (deny-listed => not trusted)
 *     become TAUTOLOGIES of the definition. They are stated in ASSERTIONS
 *     and each proves ONCE (no per-operation override PO).
 *     - dm_verified is a SET with `<:` typing, so its updates preserve the
 *       invariant by simple set reasoning -- no function-override case-split.
 *
 * WHAT IS PRESERVED (goals we already achieved):
 *   OPN-01/13/19  gpreg_writer sole-writer invariant           (unchanged)
 *   OPN-17        CCM mutex (single CCM_BUSY state)             (unchanged)
 *   OPN-18        no CCM in CARD_LOCKED/TERMINATED invariant    (unchanged)
 *   OPN-21        AUTHORIZED pre-trust  -> ASSERTION            (now a lemma)
 *   OPN-11/20     deny-list overrides   -> ASSERTION            (now a lemma)
 *   OPN-22        DM token-before-install: trusted() forces DELEGATED to be
 *                 in dm_verified, i.e. open_verify_token ran first (unchanged)
 *   OPN-02/07/15  privilege guards on requests                 (unchanged)
 *   OPN-05/06/09  DAP flag gate (dap_ok)                        (unchanged)
 *   OPN-03/16/23  still for ProB (irreversibility/reachability/animation)
 *
 * !!! UNTESTED -- cannot run Atelier B / ProB here. Re-run both. !!!
 *   RISK R1: parameterised DEFINITION trusted(aa) is only WD for aa:pending;
 *            every use sits behind aa:pending in the PRE / assertion antecedent.
 *   RISK R2: the two ASSERTIONS should close with `pp` (unfold trusted);
 *            if not, they need at most ONE small interactive step each,
 *            not per-operation.
 *   RISK R3: dm_verified typing POs (dm_verified <: pending) -- simple set
 *            inclusion; expected auto-close.
 * ===================================================================== */
MACHINE
    re_OPEN_L4_prob

SETS
    CARD_LCS  = {OP_READY, INITIALIZED, SECURED, CARD_LOCKED, TERMINATED};
    APP_LCS   = {APP_INSTALLED, APP_SELECTABLE, APP_SPECIFIC,
                 LOCKED_FROM_INSTALLED, LOCKED_FROM_SELECTABLE,
                 LOCKED_FROM_APPSPEC, APP_DELETED};
    CCM_STATE = {CCM_IDLE, CCM_BUSY};
    MGMT_MODE = {AUTHORIZED, DELEGATED};
    DECISION  = {ALLOW, DENY};
    LOCK_REQ  = {BY_ASSOC_SD, BY_GLOBALLOCK, BY_APP_SELF};
    APP_ID    = {isd, a1, a2};
    PRIVILEGE = {PRV_AM, PRV_DM, PRV_TOKEN_VERIF, PRV_GLOBAL_DELETE,
                 PRV_CARD_LOCK, PRV_CARD_TERMINATE};
    TOKEN_ID  = {tok_ok1, tok_ok2, tok_bad};
    WRITER    = {W_NONE, W_OPEN, W_SD, W_APP}

DEFINITIONS
    CM_OK == {OP_READY, INITIALIZED, SECURED};
    /* Derived trust predicate (WD only for aa : pending). */
    trusted(aa) == ( token_id(aa) /: deny_list
                     & ( req_mode(aa) = AUTHORIZED  or  aa : dm_verified ) )

ABSTRACT_VARIABLES
    card_lcs, ccm, registry, app_lcs,
    pending, req_mode, last_decision,
    privilege, dap_ok, token_id, deny_list,
    gpreg_writer, dm_verified

INVARIANT
    /* ---- typing ---- */
    card_lcs      : CARD_LCS                         &
    ccm           : CCM_STATE                        &
    registry      <: APP_ID                          &
    app_lcs       : registry --> APP_LCS             &
    pending       <: registry                        &
    req_mode      : pending --> MGMT_MODE            &
    last_decision : DECISION                         &
    privilege     : registry <-> PRIVILEGE           &
    dap_ok        : pending --> BOOL                 &
    token_id      : pending --> TOKEN_ID             &
    deny_list     <: TOKEN_ID                        &
    gpreg_writer  : WRITER                           &
    dm_verified   <: pending                         &

    /* ---- OPN-01/13/19: OPEN is the sole writer of the GP Registry ---- */
    ( gpreg_writer : {W_NONE, W_OPEN} )              &

    /* ---- OPN-18: no content-mgmt when CARD_LOCKED / TERMINATED ---- */
    ( card_lcs /: CM_OK  =>  ccm = CCM_IDLE )

ASSERTIONS
    /* OPN-21: an AUTHORIZED, non-deny-listed pending request is trusted.
     *   Proved ONCE by unfolding trusted() -- no per-operation PO. */
    !aa.( aa : pending & req_mode(aa) = AUTHORIZED
             & token_id(aa) /: deny_list  =>  trusted(aa) );
    /* OPN-11/20: a deny-listed pending request is never trusted. */
    !aa.( aa : pending & token_id(aa) : deny_list  =>  not(trusted(aa)) )

INITIALISATION
    card_lcs      := OP_READY                             ||
    ccm           := CCM_IDLE                             ||
    registry      := {isd}                                ||
    app_lcs       := {isd |-> APP_SELECTABLE}             ||
    pending       := {}                                   ||
    req_mode      := {}                                   ||
    last_decision := ALLOW                                ||
    privilege     := {isd |-> PRV_AM, isd |-> PRV_DM,
                      isd |-> PRV_TOKEN_VERIF,
                      isd |-> PRV_GLOBAL_DELETE,
                      isd |-> PRV_CARD_LOCK,
                      isd |-> PRV_CARD_TERMINATE}         ||
    dap_ok        := {}                                   ||
    token_id      := {}                                   ||
    deny_list     := {tok_bad}                            ||
    gpreg_writer  := W_NONE                               ||
    dm_verified   := {}

OPERATIONS

    /* ---------------- CARD LIFE-CYCLE (OPN-03, OPN-18) ---------------- */

    card_initialized =
        PRE card_lcs = OP_READY & ccm = CCM_IDLE THEN
            card_lcs := INITIALIZED
        END;

    card_secure =
        PRE card_lcs = INITIALIZED & ccm = CCM_IDLE THEN
            card_lcs := SECURED
        END;

    card_lock(who) =              /* OPN-08 */
        PRE card_lcs = SECURED & ccm = CCM_IDLE
            & who : registry & who |-> PRV_CARD_LOCK : privilege THEN
            card_lcs := CARD_LOCKED
        END;

    card_unlock(who) =
        PRE card_lcs = CARD_LOCKED
            & who : registry & who |-> PRV_CARD_LOCK : privilege THEN
            card_lcs := SECURED
        END;

    card_terminate(who) =         /* OPN-12 / 9.6.4: may pre-empt CCM */
        PRE card_lcs /= TERMINATED
            & who : registry & who |-> PRV_CARD_TERMINATE : privilege THEN
            card_lcs := TERMINATED || ccm := CCM_IDLE
        END;

    /* ---------------- CCM CONCURRENCY (OPN-17) ---------------- */

    ccm_start =
        PRE ccm = CCM_IDLE & card_lcs : CM_OK THEN
            ccm := CCM_BUSY
        END;

    ccm_end =
        PRE ccm = CCM_BUSY THEN
            ccm := CCM_IDLE
        END;

    /* ---------------- DENY-LIST MANAGEMENT (OPN-11/20, 9.1.3.1) ----------
     * Guard: no pending request uses this token (keeps assertions trivial).
     * Limitation: an in-use token cannot be deny-listed mid-request. */
    add_to_deny_list(tid) =
        PRE tid : TOKEN_ID
            & !aa.(aa : pending => token_id(aa) /= tid) THEN
            deny_list := deny_list \/ {tid}
        END;

    /* ---------------- CONTENT REGISTRATION (OPN-19, OPN-01/13) -------- */
    open_register_new(aa) =
        PRE aa : APP_ID & aa /: registry & ccm = CCM_BUSY THEN
            registry     := registry \/ {aa} ||
            app_lcs(aa)  := APP_INSTALLED     ||
            gpreg_writer := W_OPEN
        END;

    /* ---------------- SD REQUESTS (OPN-07, OPN-21/22) ----------------- */

    /* OPN-21: AUTHORIZED path -- manager holds AM privilege. No token_ok
     * to set: trustworthiness is derived by trusted(). */
    sd_request_authorized(mgr, aa, tid) =
        PRE mgr : registry & mgr |-> PRV_AM : privilege
            & aa : registry & aa /: pending & tid : TOKEN_ID
            & app_lcs(aa) = APP_INSTALLED THEN
            pending      := pending \/ {aa} ||
            req_mode(aa) := AUTHORIZED       ||
            token_id(aa) := tid              ||
            dap_ok(aa)   := FALSE
        END;

    /* OPN-22: DELEGATED path -- manager holds DM privilege. Not yet in
     * dm_verified, so trusted() is false until open_verify_token runs. */
    sd_request_delegated(mgr, aa, tid) =
        PRE mgr : registry & mgr |-> PRV_DM : privilege
            & aa : registry & aa /: pending & tid : TOKEN_ID
            & app_lcs(aa) = APP_INSTALLED THEN
            pending      := pending \/ {aa} ||
            req_mode(aa) := DELEGATED        ||
            token_id(aa) := tid              ||
            dap_ok(aa)   := FALSE
        END;

    /* OPN-22: on-card token verification adds aa to dm_verified, but only
     * if the token is not deny-listed (OPN-11/20 stays consistent). */
    open_verify_token(aa) =
        PRE aa : pending & req_mode(aa) = DELEGATED
            & aa /: dm_verified & token_id(aa) /: deny_list THEN
            dm_verified := dm_verified \/ {aa}
        END;

    /* OPN-20: explicit deny for a deny-listed token. */
    open_deny_denylisted(aa) =
        PRE aa : pending & token_id(aa) : deny_list THEN
            last_decision := DENY             ||
            pending       := pending - {aa}   ||
            req_mode      := {aa} <<| req_mode ||
            token_id      := {aa} <<| token_id ||
            dap_ok        := {aa} <<| dap_ok  ||
            dm_verified   := dm_verified - {aa}
        END;

    /* OPN-05/06/09/10: DAP / LFDB-signature check as a boolean gate. */
    open_verify_dap(aa) =
        PRE aa : pending & dap_ok(aa) = FALSE THEN
            dap_ok(aa) := TRUE
        END;

    /* ---------------- OPEN EXECUTES : single writer (OPN-01/13) ---------
     * Guard uses derived trusted(aa) (WD: aa:pending is first). 9.3.3:
     * OPEN assigns privileges to the installed entity. */
    /* ProB variant: single privilege parameter (6 values) instead of a
     * subset (64) -- shrinks the state-space so projection/animation run.
     * Behaviourally equivalent for FSM checking; use L4 (subset) for the
     * Atelier B proof of record. */
    open_install(aa, priv) =
        PRE aa : pending & trusted(aa) & dap_ok(aa) = TRUE
            & ccm = CCM_BUSY & app_lcs(aa) = APP_INSTALLED
            & priv : PRIVILEGE THEN
            app_lcs(aa)   := APP_SELECTABLE          ||
            privilege     := privilege \/ {aa |-> priv} ||  /* 9.3.3 */
            gpreg_writer  := W_OPEN                   ||     /* OPN-01/13/19 */
            last_decision := ALLOW                   ||
            pending       := pending - {aa}          ||
            req_mode      := {aa} <<| req_mode        ||
            token_id      := {aa} <<| token_id        ||
            dap_ok        := {aa} <<| dap_ok          ||
            dm_verified   := dm_verified - {aa}
        END;

    /* SELECTABLE <-> Application-specific (App itself). */
    app_enter_specific(aa) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SELECTABLE THEN
            app_lcs(aa) := APP_SPECIFIC
        END;

    app_leave_specific(aa) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SPECIFIC THEN
            app_lcs(aa) := APP_SELECTABLE
        END;

    /* ---- LOCK / UNLOCK : LOCKED-from-* remembers origin (5.3.1.3) ---- */

    app_lock_from_installed(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_INSTALLED
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := LOCKED_FROM_INSTALLED
        END;

    app_unlock_to_installed(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = LOCKED_FROM_INSTALLED
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := APP_INSTALLED
        END;

    app_lock_from_selectable(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SELECTABLE
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK, BY_APP_SELF} THEN
            app_lcs(aa) := LOCKED_FROM_SELECTABLE
        END;

    /* unlock stricter: App_self excluded (9.6.2 / 5.3.1.3) */
    app_unlock_to_selectable(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = LOCKED_FROM_SELECTABLE
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := APP_SELECTABLE
        END;

    app_lock_from_appspec(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = APP_SPECIFIC
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK, BY_APP_SELF} THEN
            app_lcs(aa) := LOCKED_FROM_APPSPEC
        END;

    app_unlock_to_appspec(aa, who) =
        PRE aa : registry & ccm = CCM_BUSY & app_lcs(aa) = LOCKED_FROM_APPSPEC
            & who : {BY_ASSOC_SD, BY_GLOBALLOCK} THEN
            app_lcs(aa) := APP_SPECIFIC
        END;

    /* ---- DELETE from any non-deleted state (OPN-23) ---- */
    open_delete(aa) =
        PRE aa : registry & aa /: pending & ccm = CCM_BUSY
            & app_lcs(aa) /= APP_DELETED THEN
            app_lcs(aa) := APP_DELETED
        END;

    /* ---------------- TERMINAL SELF-LOOP (OPN-18) ---------------- */
    terminated_end =
        PRE card_lcs = TERMINATED THEN
            skip
        END

END
