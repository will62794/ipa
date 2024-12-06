import tlaparse
import graphviz
import sys
import subprocess
import itertools

# specname = "Paxos"
specname = "RaftAbstractDynamic"
specname = "AsyncRaft"
specname = "consensus_epr"
specname = "M_uni"
specname = sys.argv[1]

my_spec = tlaparse.parse_tla_file(specname, specname)

top_level_defs = my_spec.get_all_user_defs(level="1")
spec_obj = my_spec.get_spec_obj()
print(f"Found {len(top_level_defs)} top level defs.")
# for d in top_level_defs:
#     print(" ", d)

actions_from_spec = []
for udef in my_spec.get_all_user_defs(level="2"):
    if udef.endswith("Action"):
        actions_from_spec.append(udef)
        # print(udef)


action_interaction_vars = {a.replace("Action", ""):{} for a in actions_from_spec}
for action in actions_from_spec:
    vars_in_action,action_updated_vars = my_spec.get_vars_in_def(action)
    ret = my_spec.get_action_var_info(action)
    print(action, ret)
    action_interaction_vars[action.replace("Action", "")] = ret


# print("--")
# action_interaction_vars = {a.replace("Action", ""):{"rvars":[], "wvars":[]} for a in actions_from_spec}
# print(action_interaction_vars)
# for udef in my_spec.get_all_user_defs(level="1"):
#     if "RVars" in udef:
#         print(udef, my_spec.get_vars_in_def(udef)[0])
#         action_interaction_vars[udef.replace("RVars", "")]["rvars"] = (my_spec.get_vars_in_def(udef)[0])
#     if "WVars" in udef:
#         print(udef, my_spec.get_vars_in_def(udef)[0])
#         action_interaction_vars[udef.replace("WVars", "")]["wvars"] = (my_spec.get_vars_in_def(udef)[0])
# print("Interaction graph:")
# for a in action_interaction_vars:
#     print(a, action_interaction_vars[a])

# Generate DOT digraph that reports an edge between action nodes if the two actions interact i.e.
# A1 reads from a variable that A2 writes to. Also include along the edges the interaction variables.
dot = graphviz.Digraph(comment='Action Interaction Graph')
dot.attr(rankdir='LR')
# dot.attr(nodesep='0.1')


# Add nodes for each action
for action in action_interaction_vars:
    dot.node(action, shape='box', style='rounded')
    print(action, action_interaction_vars[action]["write_dep_vars"])

# Add edges between actions that interact
for action1 in action_interaction_vars:
    for action2 in action_interaction_vars:
        if action1 == action2:
            continue
            
        # Find variables that action1 reads and action2 writes
        interaction_vars = set(action_interaction_vars[action1]["read_vars"]) & \
                         set(action_interaction_vars[action2]["write_vars"])
                         
        if interaction_vars:
            # Create edge with interaction variables as label
            dot.edge(action2, action1, 
                    label=f"{','.join(interaction_vars)}", 
                    fontsize='12')

# Save the graph
dot.attr(dpi='300')
dot.render(f'{specname}/{specname}_interaction_graph', view=False)
dot.render(f'{specname}/{specname}_interaction_graph', view=False, format='png')


# Independence == 
#     \* Action2 cannot disable Action1.
#     /\ [][((ENABLED Action1 /\ Action2 ) => (Action1pre)')]_vars
#     \* Action2 cannot enable Action1.
#     /\ [][((~ENABLED Action1 /\ Action2 ) => (~Action1pre)')]_vars
#     \* Action1 cannot disable Action2.
#     /\ [][((ENABLED Action2 /\ Action1 ) => (Action2pre)')]_vars
#     \* Action1 cannot enable Action2.
#     /\ [][((~ENABLED Action2 /\ Action1 ) => (~Action2pre)')]_vars

def compute_semantic_interactions(spec_actions):
    print("Computing semantic interactions")
    semantic_interaction_edges = []
    # Check semantic interaction between actions.
    for action1, action2 in itertools.product(spec_actions, spec_actions):
        if action1 == action2:
            continue

        if "RMRcvCommitMsgAction" not in [action1,action2] or "RMRcvAbortMsgAction" not in [action1,action2]:
            continue

        template = ""
        modname = f"{specname}_interaction"
        template += f"---- MODULE {modname} ----\n"
        template += f"EXTENDS {specname}\n"
        template += "\n"

        template += "VARIABLE tookStep\n"
        template += "VARIABLE wasEnabled\n"
        template += "VARIABLE varsPrev\n"
        template += "\n"

        template += "Action1 == TRUE\n"
        template += f"Action2 == TRUE\n"
        template += f"Action1pre == TRUE\n"
        template += f"Action2pre == TRUE\n"
        template += f"Action1PostExprs == TRUE\n"
        template += f"Action2PostExprs == TRUE\n"
        template += "\n"

        template += "InteractionInit == \n"
        template += "  /\ TypeOK\n"
        template += "  /\ wasEnabled = FALSE\n"
        template += "  /\ tookStep = FALSE\n"
        template += "  /\ varsPrev = <<>>\n"
        template += "\n"

        # Really, we shouldn't be considering commutativity based on writes to *all* variables e.g.
        # if two actions have no overlap in their variable read/write sets, then they naturally shouldn't
        # be considered as "interacting". So, rather, to check whether Action1 interacts with Action2, we
        # only consider the intersection of variables Action2 reads from.
        a2_read_vars = action_interaction_vars[action2.replace("Action", "")]["write_dep_vars"]
        template += f"Action2_read_vars == <<{','.join(a2_read_vars)}>>\n"
        template += "\n"

        template += "InteractionNext == \n"
        template += "  /\ Action1\n"
        template += "  /\ wasEnabled' = ENABLED Action2\n"
        template += "  /\ tookStep' = TRUE\n"

        # Really, we shouldn't be considering commutativity based on writes to *all* variables e.g.
        # if two actions have no overlap in their variable read/write sets, then they naturally shouldn't
        # be considered as "interacting". So, rather, to check whether Action1 interacts with Action2, we
        # only consider the intersection of variables Action2 reads from.
        template += f"  /\ varsPrev' = Action2_read_vars\n"
        template += "\n"

        # Independence conditions (does Action 1 enable/disable Action 2).
        cannot_disable_conds = [
            # "[][(Action1 /\ Action2pre) => (Action2pre')]_vars",
            "(tookStep /\ wasEnabled) => ENABLED Action2"
        ]
        template += "\n"
        template += "CannotDisable == \n"
        for cannot_disable_cond in cannot_disable_conds:
            template += f"    /\ {cannot_disable_cond}\n"

        cannot_enable_conds = [   
            # "[][(Action1 /\ ~Action2pre) => (~Action2pre')]_vars",
            "(tookStep /\ ~wasEnabled) => (~ENABLED Action2)"
        ]
        template += "\n"
        template += "CannotEnable == \n"
        for cannot_enable_cond in cannot_enable_conds:
            template += f"    /\ {cannot_enable_cond}\n"

        # Commutativity conditions.
        # Does Action 1 commute with Action 2.
        comm_conds = [
            # "[][Action1 => Action2PostExprs = Action2PostExprs']_vars",
            "tookStep => (varsPrev = Action2_read_vars)"
        ]
        template += "\n"
        template += "Commutativity == \n"
        for comm_cond in comm_conds:
            template += f"    /\ {comm_cond}\n"
        template += "\n"
        template += "======"

        f = open(f"{specname}/{specname}_interaction.tla", "w")
        f.write(template)
        f.close()

        fcfg = open(f"{specname}/{specname}_interaction.cfg", "w")
        fcfg.write(f"INIT  InteractionInit\n")
        fcfg.write(f"NEXT  InteractionNext\n")
        fcfg.write(f"CONSTANTS\n")
        fcfg.write(f"Action1 <- {action1}\n")
        fcfg.write(f"Action2 <- {action2}\n")
        # fcfg.write(f"Action1pre <- {action1.replace('Action', '')}pre\n")
        # fcfg.write(f"Action2pre <- {action2.replace('Action', '')}pre\n")
        # fcfg.write(f"Action1PostExprs <- {action1.replace('Action', '')}PostExprs\n")
        # fcfg.write(f"Action2PostExprs <- {action2.replace('Action', '')}PostExprs\n")

        if "Paxos" in specname:
            fcfg.write("TypeOK <- TypeOKRandom\n")

        # TwoPhase.
        fcfg.write("RM = {r1,r2,r3}\n")

        # consensus_epr
        if "consensus_epr" in specname: 
            fcfg.write("\* consensus_epr\n")
            fcfg.write("Node = {n1,n2}\n")
            fcfg.write("Value = {v1,v2}\n")

        # Paxos
        if "Paxos" in specname:
            fcfg.write("\* Paxos\n")
            fcfg.write("Acceptor = {a1,a2}\n")
            fcfg.write("Ballot = {0,1}\n")
            fcfg.write("None = None\n")
            fcfg.write("Value = {v1,v2}\n")

        if "RaftAbstractDynamic" in specname:
            fcfg.write("Server = {s1,s2}\n")
            fcfg.write("Nil = Nil\n")
            fcfg.write("Secondary = Secondary\n")
            fcfg.write("Primary = Primary\n")
            fcfg.write("MaxLogLen = 2\n")
            fcfg.write("MaxTerm = 2\n")
            fcfg.write("Nat = {0,1,2}\n")
            fcfg.write("MaxConfigVersion = 2\n")
            fcfg.write("InitTerm = 0\n")
            fcfg.write("CONSTRAINT StateConstraint\n")

        if "Bakery" in specname:
            fcfg.write("N = 2\n")
            fcfg.write("Nat = {0,1,2}\n")

        # fcfg.write(f"PROPERTIES\n")
        fcfg.write(f"INVARIANTS\n")
        fcfg.write(f" CannotDisable\n")
        fcfg.write(f" CannotEnable\n")
        fcfg.write(f" Commutativity\n")

        fcfg.close()

        # Run TLC from the specs directory
        print(f"Checking interaction with TLC for actions {action1} and {action2}")
        metadir = f"states/interaction_{action1}_{action2}"
        simulate = ""
        if "Paxos" in specname:
            simulate = "-simulate num=10000 -depth 4"
        cmd = f"java -cp /usr/local/tla2tools-v1.8.jar tlc2.TLC -workers 4 -maxSetSize 10000000 {simulate} -noGenerateSpecTE -deadlock -metadir {metadir} {specname}_interaction"
        print(cmd)
        subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=specname)
        res = subproc.wait()
        out_lines = subproc.stdout.readlines()
        interaction = False
        for line in (out_lines):
            if "is violated" in str(line):
                interaction = True
            # if "No error has been found" in str(line):
                # interaction = False
        if interaction:
            print(f"Semantic interaction between {action1} and {action2}")
            semantic_interaction_edges.append((action1, action2))

        print("----")

        # Re-generate DOT digraph that reports an edge between semantically interacting action nodes.
        dot = graphviz.Digraph(comment='Semantic Action Interaction Graph')
        dot.attr(rankdir='LR')
        # dot.attr(nodesep='0.1')

        # Add nodes for each action
        for action in actions_from_spec:
            dot.node(action.replace("Action", ""), shape='box', style='rounded')
        
        for action1, action2 in semantic_interaction_edges:
            # dot.edge(action2, action1, label=f"{','.join(interaction_vars)}", fontsize='12')

            # Find variables that action1 reads and action2 writes
            # Does Action1's writes interact with Action2's reads.
            interaction_vars = set(action_interaction_vars[action1.replace("Action", "")]["write_vars"]) & set(action_interaction_vars[action2.replace("Action", "")]["read_vars"])
            label = ""
            if interaction_vars:
                # Create edge with interaction variables as label
                label = f"{','.join(interaction_vars)}"
                # dot.edge(action2, action1, 
                #         label=f"{','.join(interaction_vars)}", 
                #         fontsize='12')
            dot.edge(action1.replace("Action", ""), action2.replace("Action", ""), label=label, fontsize='12')


        dot.attr(dpi='300')
        dot.render(f'{specname}/{specname}_semantic_interaction_graph', view=False)
        dot.render(f'{specname}/{specname}_semantic_interaction_graph', view=False, format='png')

compute_semantic_interactions(actions_from_spec)