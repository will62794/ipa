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

# Add nodes for each action
for action in action_interaction_vars:
    dot.node(action, shape='box', style='rounded')

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

# Check semantic interaction between actions.
for action1, action2 in itertools.product(actions_from_spec, actions_from_spec):
    if action1 == action2:
        continue

    template = ""
    modname = f"{specname}_interaction"
    template += f"---- MODULE {modname} ----\n"
    template += f"EXTENDS {specname}\n"
    template += "\n"

    template += "Action1 == TRUE\n"
    template += f"Action2 == TRUE\n"
    template += f"Action1pre == TRUE\n"
    template += f"Action2pre == TRUE\n"
    template += f"Action1PostExprs == TRUE\n"
    template += f"Action2PostExprs == TRUE\n"
    template += "\n"

    template += "InteractionInit == TypeOK\n"
    template += "InteractionNext == Action1 \/ Action2\n"
    template += "\n"

    # Independence conditions.
    indep_conds = [
        "[][((ENABLED Action1 /\ Action2 ) => (Action1pre)')]_vars",
        "[][((~ENABLED Action1 /\ Action2 ) => (~Action1pre)')]_vars",
        "[][((ENABLED Action2 /\ Action1 ) => (Action2pre)')]_vars",
        "[][((~ENABLED Action2 /\ Action1 ) => (~Action2pre)')]_vars",
    ]
    template += "\n"
    template += "Independence == \n"
    for indep_cond in indep_conds:
        template += f"    /\ {indep_cond}\n"

    # Commutativity conditions.
    comm_conds = [
        "[][Action1 => Action2PostExprs = Action2PostExprs']_vars",
        "[][Action2 => Action1PostExprs = Action1PostExprs']_vars",
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
    fcfg.write(f"Action1pre <- {action1.replace('Action', '')}pre\n")
    fcfg.write(f"Action2pre <- {action2.replace('Action', '')}pre\n")
    fcfg.write(f"Action1PostExprs <- {action1.replace('Action', '')}PostExprs\n")
    fcfg.write(f"Action2PostExprs <- {action2.replace('Action', '')}PostExprs\n")
    fcfg.close()

    # Run TLC from the specs directory
    print(f"Checking interaction with TLC for actions {action1} and {action2}")
    cmd = f"java -cp ../tla2tools.jar tlc2.TLC {specname}_interaction"
    subproc = subprocess.Popen(cmd, shell=True, stdout=subprocess.PIPE, cwd=specname)
    res = subproc.wait()
    print(res)



    # print(template)
