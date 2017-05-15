#include "ebc.h"

#include "agent.h"
#include "condition.h"
#include "dprint.h"
#include "instantiation.h"
#include "mem.h"
#include "preference.h"
#include "slot.h"
#include "symbol.h"
#include "test.h"

/* ------------------------------------------------------------------
                  Add a preference to a slot's OSK prefs
   This function adds a preference to a slots's context dependent
   preference set, checking to first see whether the pref is already
   there. If an operator The slot's OSK prefs is copied to conditions' bt structs in
   create_instatiation.  Those copies of the OSK prefs are used to
   backtrace through all relevant local evaluation rules that led to the
   selection of the operator that produced a result.
------------------------------------------------------------------ */
void Explanation_Based_Chunker::add_to_OSK(slot* pSlot, preference* pPref, bool unique_value)
{

    bool already_exists = false;
    cons* lOSK_pref;
    preference* lPref;

    for (lOSK_pref = pSlot->OSK_prefs; lOSK_pref != NIL; lOSK_pref = lOSK_pref->rest)
    {
        lPref = static_cast<preference*>(lOSK_pref->first);
        if (lPref == pPref)
        {
            already_exists = true;
            break;
        }

        if (unique_value)
        {
            /* Checking if a preference is unique differs depending on the preference type */

            /* Binary preferences can be considered equivalent if they point to the same
             * operators in the correct relative spots */
            if (((pPref->type == BETTER_PREFERENCE_TYPE) || (pPref->type == WORSE_PREFERENCE_TYPE)) &&
                    ((lPref->type == BETTER_PREFERENCE_TYPE) || (lPref->type == WORSE_PREFERENCE_TYPE)))
            {
                if (pPref->type == lPref->type)
                {
                    already_exists = ((pPref->value == lPref->value) && (pPref->referent == lPref->referent));
                }
                else
                {
                    already_exists = ((pPref->value == lPref->referent) && (pPref->referent == lPref->value));
                }
            }
            else if ((pPref->type == BINARY_INDIFFERENT_PREFERENCE_TYPE) &&
                     (lPref->type == BINARY_INDIFFERENT_PREFERENCE_TYPE))
            {
                already_exists = (((pPref->value == lPref->value) && (pPref->referent == lPref->referent)) ||
                                  ((pPref->value == lPref->referent) && (pPref->referent == lPref->value)));
            }
            else
            {
                /* Otherwise they are equivalent if they have the same value and type */
                already_exists = (pPref->value == lPref->value) && (pPref->type == lPref->type);
            }
            if (already_exists)
            {
                break;
            }
        }
    }
    if (!already_exists)
    {
        push(thisAgent, pPref, pSlot->OSK_prefs);
        preference_add_ref(pPref);
    }
}


/* --------------------------------------------------------------------------
                 Build context-dependent preference set

  This function will copy the OSK prefs from a slot to the backtrace info for the
  corresponding condition.  The copied OSK prefs will later be backtraced through.

  Note: Until prohibits are included explicitly as part of the OSK prefs, we will
  just copy them directly from the prohibits list so that there is no
  additional overhead.

 --------------------------------------------------------------------------*/

void Explanation_Based_Chunker::copy_proposal_OSK(instantiation* inst, cons* newOSK)
{
    preference* pref;
    cons* l_OSK_prefs;

    assert (!inst->OSK_proposal_prefs);
    if (ebc_settings[SETTING_EBC_ADD_OSK])
    {
        for (l_OSK_prefs = newOSK; l_OSK_prefs != NIL; l_OSK_prefs = l_OSK_prefs->rest)
        {
            pref = static_cast<preference*>(l_OSK_prefs->first);
            push(thisAgent, pref, inst->OSK_proposal_prefs);
            dprint(DT_OSK, "Adding OSK proposal preference %p to instantiation.\n",  pref);
            /* Note that we don't add refcount to the preference here. If we did, this 
             * instantiation would never be deallocated since it will hold a refcount
             * on one of its own preferences.  */
        }
    }
}

void Explanation_Based_Chunker::copy_OSK(instantiation* inst)
{
    condition* cond;
    preference* pref;
    cons* l_OSK_prefs;

    inst->OSK_prefs = NIL;
    for (cond = inst->top_of_instantiated_conditions; cond != NIL; cond = cond->next)
    {
        if (cond->type == POSITIVE_CONDITION && cond->bt.trace && cond->bt.trace->slot)
        {
            if (ebc_settings[SETTING_EBC_ADD_OSK])
            {
                if (cond->bt.trace->slot->OSK_prefs && (cond->data.tests.id_test->eq_test->data.referent->id->level == inst->match_goal_level) && !cond->test_for_acceptable_preference)
                {
                    for (l_OSK_prefs = cond->bt.trace->slot->OSK_prefs; l_OSK_prefs != NIL; l_OSK_prefs = l_OSK_prefs->rest)
                    {
                        pref = static_cast<preference*>(l_OSK_prefs->first);
                        push(thisAgent, pref, inst->OSK_prefs);
                        dprint(DT_OSK, "Adding OSK preference %p to instantiation.\n",  pref);
                        preference_add_ref(pref);
                    }
                }
            }
            pref = cond->bt.trace->slot->preferences[PROHIBIT_PREFERENCE_TYPE];
            while (pref)
            {
                push(thisAgent, pref, inst->OSK_prefs);
                preference_add_ref(pref);
                dprint(DT_OSK, "Adding OSK prohibit preference %p to instantiation.\n",  pref);
                pref = pref->next;
            }
        }
    }
}

void Explanation_Based_Chunker::update_proposal_OSK(slot* s, preference* winner)
{
    if (s->instantiation_with_temp_OSK)
    {
        dprint(DT_OSK, "Cleaning up OSK proposal preferences contained in inst %u (%y) %s\n",  s->instantiation_with_temp_OSK->i_id,  s->instantiation_with_temp_OSK->prod_name, s->instantiation_with_temp_OSK->OSK_proposal_prefs ? "exists" : "NULL");
        /* These prefs did not have their refcounts increased, so we don't want to call clear_preference_list */
        free_list(thisAgent, s->instantiation_with_temp_OSK->OSK_proposal_prefs);
        s->instantiation_with_temp_OSK->OSK_proposal_prefs = NULL;
        s->instantiation_with_temp_OSK->OSK_proposal_slot = NULL;
        s->instantiation_with_temp_OSK = NULL;
    }
    if (winner)
    {
        s->instantiation_with_temp_OSK = winner->inst;
        s->instantiation_with_temp_OSK->OSK_proposal_slot = s;
        dprint(DT_OSK, "Adding OSK proposal preferences contained to inst %u (%y) from slot (%y ^%y)\n",  s->instantiation_with_temp_OSK->i_id,  s->instantiation_with_temp_OSK->prod_name, s->id, s->attr);
        copy_proposal_OSK(winner->inst, s->OSK_prefs);
    }
}

void Explanation_Based_Chunker::generate_relevant_OSK(slot* s, preference* winner)
{
    if (winner)
    {
        if (s->all_preferences->all_of_slot_next)
        {
//            /* If there are reject or prohibit preferences, then
//             * add all reject and prohibit preferences to OSK prefs */
//
//            if (s->preferences[PROHIBIT_PREFERENCE_TYPE] || s->preferences[REJECT_PREFERENCE_TYPE])
//            {
//                for (p = s->preferences[PROHIBIT_PREFERENCE_TYPE]; p != NIL; p = p->next)
//                {
//                    thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                }
//                for (p = s->preferences[REJECT_PREFERENCE_TYPE]; p != NIL; p = p->next)
//                {
//                    thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                }
//            }
//
//            /* Add better/worse preferences to OSK prefs */
//            for (p = s->preferences[BETTER_PREFERENCE_TYPE]; p != NIL; p = p->next)
//            {
//                if (p->value == cand->value)
//                {
//                    thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                }
//            }
//            for (p = s->preferences[WORSE_PREFERENCE_TYPE]; p != NIL; p = p->next)
//            {
//                if (p->referent == cand->value)
//                {
//                    thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                }
//            }
//            for (p = s->preferences[BEST_PREFERENCE_TYPE]; p != NIL; p = p->next)
//            {
//                if (p->value == cand->value)
//                {
//                    thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                }
//            }
//            /* Because we only want to add worst preferences to the OSK prefs if they actually have an impact
//            * on the candidate list, we must first see if there's at least one non-worst candidate. */
//
//            if (add_OSK)
//            {
//                some_not_worst = false;
//                for (cand = candidates; cand != NIL; cand = cand->next_candidate)
//                {
//                    if (cand->value->decider_flag != WORST_DECIDER_FLAG)
//                    {
//                        some_not_worst = true;
//                    }
//                }
//            }
//            if (add_OSK && some_not_worst)
//            {
//                /* Add this worst preference to OSK prefs */
//                for (p = s->preferences[WORST_PREFERENCE_TYPE]; p != NIL; p = p->next)
//                {
//                    if (p->value == cand->value)
//                    {
//                        thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                    }
//                }
//            }
//            if (add_OSK)
//            {
//
//                /* Add all indifferent preferences associated with the chosen candidate to the OSK prefs.*/
//
//                if (some_numeric)
//                {
//
//                    /* Note that numeric indifferent preferences are never considered duplicates, so we
//                    * pass an extra argument to add_to_OSK so that it does not check for duplicates.*/
//
//                    for (p = s->preferences[NUMERIC_INDIFFERENT_PREFERENCE_TYPE]; p != NIL; p = p->next)
//                    {
//                        if (p->value == (*result_candidates)->value)
//                        {
//                            thisAgent->explanationBasedChunker->add_to_OSK(s, p, false);
//                        }
//                    }
//
//                    /* Now add any binary preferences with a candidate that does NOT have a numeric preference. */
//
//                    for (p = s->preferences[BINARY_INDIFFERENT_PREFERENCE_TYPE]; p != NIL; p = p->next)
//                    {
//                        if ((p->value == (*result_candidates)->value) || (p->referent == (*result_candidates)->value))
//                        {
//                            if ((p->referent->decider_flag != UNARY_INDIFFERENT_CONSTANT_DECIDER_FLAG) ||
//                                    (p->value->decider_flag != UNARY_INDIFFERENT_CONSTANT_DECIDER_FLAG))
//                            {
//                                thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                            }
//                        }
//                    }
//                }
//                else
//                {
//
//                    /* This decision was non-numeric, so add all non-numeric preferences associated with the
//                     * chosen candidate to the OSK prefs.*/
//
//                    /* Note:  We've disabled unary indifferents because they were causing problems in certain demo agents
//                     *        All of the OSK prefs that involve uncertainty now seem weird. Will need to reconsider how
//                     *        we handle them now  that we have a better handle for correctness issues and are thinking
//                     *        about the possibility of probabilistic chunks.*/
//
////                    for (p = s->preferences[UNARY_INDIFFERENT_PREFERENCE_TYPE]; p != NIL; p = p->next)
////                    {
////                        if (p->value == (*result_candidates)->value)
////                        {
////                            thisAgent->explanationBasedChunker->add_to_OSK(s, p);
////                        }
////                    }
//                    for (p = s->preferences[BINARY_INDIFFERENT_PREFERENCE_TYPE]; p != NIL; p = p->next)
//                    {
//                        if ((p->value == (*result_candidates)->value) || (p->referent == (*result_candidates)->value))
//                        {
//                            thisAgent->explanationBasedChunker->add_to_OSK(s, p);
//                        }
//                    }
//                }
//            }

        } else {
            /* Only one preference determined this winner */
        }
    }
    update_proposal_OSK(s, winner);
}
