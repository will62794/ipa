import tlaparse
import graphviz

# specname = "Paxos"
specname = "RaftAbstractDynamic"
specname = "AsyncRaft"
specname = "consensus_epr"

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
dot.render(f'{specname}_interaction_graph', view=True)
dot.render(f'{specname}_interaction_graph', view=False, format='png')




