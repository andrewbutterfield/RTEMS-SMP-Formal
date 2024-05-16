import os
import re


def natural_sort_key(s):
    parts = re.split('([0-9]+)', s)
    for i in range(len(parts)):
        if parts[i].isdigit():
            parts[i] = int(parts[i])
        else:
            parts[i] = parts[i].lower()
    return parts


def check_order(lines, order, must_not_contain=None, start_index=0, end_index=None):
    order_index = 0
    for i in range(start_index, end_index if end_index else len(lines)):
        if must_not_contain and any(unwanted in lines[i] for unwanted in must_not_contain):
            return False 
        if order_index < len(order) and order[order_index] in lines[i]:
            order_index += 1
            if order_index == len(order):
                return True, i
    return False, None
    

def extract_sub_scenario(lines):
    for line in lines:
        if "@@@ 0 LOG sub-scenario created, testing" in line:
            return line.strip()
    return None


def extract_log_section(log_lines, scenario_id):
    start_marker = f"B:RtemsModelSemMgr{scenario_id}"
    end_marker = f"E:RtemsModelSemMgr{scenario_id}"
    start_index = end_index = None
    for i, line in enumerate(log_lines):
        if start_marker in line:
            start_index = i
        elif end_marker in line:
            end_index = i
            break
    if start_index is not None and end_index is not None:
        return log_lines[start_index:end_index]
    return []



def classify_file(filepath):
    with open(filepath, 'r') as file:
        lines = file.readlines()
    sub_scenario_log = extract_sub_scenario(lines)
    if not sub_scenario_log:
        return "No sub-scenario log found", False
    # Expected patterns for the three priority orders
    orders = {
        "testing no locking - priority inversion": [
            "@@@ 3 CALL sema_obtain",
            "@@@ 4 CALL sema_obtain",
            "@@@ 3 SIGNAL 1",
            "@@@ 5 ",
            "@@@ 3 CALL sema_release",
            "@@@ 4 CALL sema_release"
        ],
        "testing priority inheritance protocol": [
            "@@@ 3 CALL sema_obtain",
            "@@@ 4 CALL sema_obtain",
            "@@@ 3 LOG tasks[TASK1_ID].effectivePriority 1",
            "@@@ 3 CALL sema_release",
            "@@@ 4 CALL sema_release"
        ],
        "testing priority ceiling protocol": [
            "@@@ 3 CALL sema_obtain",
            "@@@ 3 STATE 1 Ready",
            "@@@ 3 CALL sema_release",
            "@@@ 4 CALL sema_obtain",
            "@@@ 4 CALL sema_release"
        ]
    }
    for order_name, order_sequence in orders.items():
        match, _ = check_order(lines, order_sequence)
        if match:
            return sub_scenario_log, True
    return sub_scenario_log, False


def analyze_priority_in_files(directory):
    spn_files = [f for f in os.listdir(directory) if f.endswith('.spn')]
    spn_files.sort(key=natural_sort_key)
    matching_files = []
    for filename in spn_files:
        filepath = os.path.join(directory, filename)
        sub_scenario_log, match = classify_file(filepath)
        if match:
            matching_files.append(filepath)
        # print(f"{filename}: Sub-scenario - {sub_scenario_log}, Match: {'True' if match else 'False'}")
    return matching_files


def compare_spn_with_log(spn_files, log_filepath):
    with open(log_filepath, 'r') as log_file:
        log_lines = log_file.readlines()
    for filepath in spn_files:
        with open(filepath, 'r') as file:
            sp_lines = file.readlines()

        match = re.search(r"(\d+)\.spn$", filepath)
        scenario_id = int(match.group(1))
        log_section = extract_log_section(log_lines, scenario_id)
        # Expected order of operations in the actual RTEMS code
        orders = {
            "priority inversion": [
                "@@@ 3 CALL sema_obtain",
                "@@@ 4 CALL sema_obtain",
                "@@@ 5 CALL sema_ident",
                "@@@ 3 CALL sema_release",
                "@@@ 4 CALL sema_release"
            ],
            "priority inheritance protocol": [
                "@@@ 3 CALL sema_obtain",
                "@@@ 4 CALL sema_obtain",
                "@@@ 3 CALL sema_release",
                "@@@ 4 CALL sema_release",
                "@@@ 5 CALL sema_ident"
            ],
            "immediate ceiling priority  protocol": [
                "@@@ 3 CALL sema_obtain",
                "@@@ 3 CALL sema_release",
                "@@@ 4 CALL sema_obtain",
                "@@@ 4 CALL sema_release",
                "@@@ 5 CALL sema_ident"
            ]
        }
        if log_section:
            match_found = False
            for order_name, order_sequence in orders.items():
                match, _ = check_order(log_section, order_sequence)
                if match:
                    print(f"{filepath}: {order_name} - correct order")
                    match_found = True
                    break
            if not match_found:
                print(f"{filepath}: incorrect order")
        else:
            print(f"{filepath}: No corresponding log section found")



directory = '.'
log_filepath = 'sem-model-0-test.log'
matching_spn_files = analyze_priority_in_files(directory)
compare_spn_with_log(matching_spn_files, log_filepath)
