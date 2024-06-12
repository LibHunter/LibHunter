# 构建库对象
import csv
import datetime
import hashlib
import os
import re

from androguard.core.analysis.analysis import Analysis, MethodAnalysis, MethodClassAnalysis, DVMBasicBlock
from androguard.core.bytecodes.dvm import DalvikVMFormat, EncodedMethod
from androguard.decompiler.dad.dataflow import build_def_use
from androguard.decompiler.dad.decompile import DvMethod
from androguard.decompiler.dad.graph import construct
from androguard.decompiler.dad.instruction import AssignExpression, InvokeRangeInstruction, Param
from androguard.util import read
from util import valid_method_name, instruction_size_map

filter_record_limit = 10
abstract_method_weight = 3 


class ThirdLib(object):

    def __init__(self, lib_path, logger):
        self.LOGGER = logger
        self.lib_name = None  
        self.lib_package_name = None 

        self.lib_opcode_num = int() 
        self.classes_dict = dict()  
        self.nodes_dict = dict()  
        self.lib_method_num = int()  
        # self.invoke_other_methodes = set()  
        self.interface_lib = True  
        self.condition_jump_ins = [
            'if-eq',  # == Jump if equal to a specific value
            'if-ne',  # != Jump if not equal to a specific value
            'if-lt',  # < Jump if less than a specific value
            'if-ge',  # >= Jump if greater than or equal to a specific value
            'if-gt',  # > Jump if greater than a specific value
            'if-le',  # <= Jump if less than or equal to a specific value
            'if-eqz',  # ==0 Jump if equal to zero
            'if-nez',  # !=0 Jump if not equal to zero
            'if-ltz',  # <0 Jump if less than zero
            'if-gez',  # >=0 Jump if greater than or equal to zero
            'if-gtz',  # >0 Jump if greater than zero
            'if-lez'  # <=0 Jump if less than or equal to zero
        ]
        self.half_condition_jump_ins = [
            'if-eq',  # == Jump if equal to a specific value
            'if-lt',  # < Jump if less than a specific value
            'if-le',  # <= Jump if less than or equal to a specific value
            'if-eqz',  # ==0 Jump if equal to zero
            'if-ltz',  # <0 Jump if less than zero
            'if-lez'  # <=0 Jump if less than or equal to zero
        ]

        # Parse the dex1 file corresponding to lib when initializing the ThirdLib object.
        self.LOGGER.debug("Starting to parse %s ..." , os.path.basename(lib_path))
        self._parse_lib(lib_path)
        self.LOGGER.debug("%s parsing complete", os.path.basename(lib_path))

    def analysis_callee_arguments_wapper(self, dex_obj, analysis_obj):
        callsites_arguments = {}
        for cls in dex_obj.get_classes():
            for method in cls.get_methods():
                if method.code_off == 0:
                    continue
                mx: MethodAnalysis = analysis_obj.get_method(method)
                dv_method: DvMethod = DvMethod(mx)
                try:
                    graph = construct(dv_method.start_block, dv_method.var_to_name, dv_method.exceptions)
                    use_defs, _ = build_def_use(graph, dv_method.lparams)
                except Exception as e:
                    self.LOGGER.error('Raise an Error in method {}: {}, Skip it'.format(method.full_name, e))
                    continue
                self.analysis_callee_arguments(graph, use_defs, callsites_arguments)
        return callsites_arguments

    def analysis_callee_arguments(self, graph, use_defs, callsites_arguments):
        """
        Analyze the arguments of the callee method in the graph
        """

        for index, stmt in graph.loc_to_ins.items():
            if isinstance(stmt, AssignExpression):
                if stmt.is_call():
                    rhs = stmt.get_rhs()
                    if isinstance(rhs, InvokeRangeInstruction):
                        continue

                    # if rhs.cls.startswith('java'):
                    #     continue
                    if '.' not in rhs.cls:
                        continue
                    callee = '{}.{}({}){}'.format(rhs.cls, rhs.name, ''.join(rhs.ptype), rhs.rtype)

                    for var in rhs.args:
                        var_index = rhs.args.index(var)
                        defs = use_defs[(var, index)]
                        if len(defs) != 1:
                            continue
                        def_index = defs[0]
                        if def_index < 0:
                            # this is a param, set NAC
                            if callee not in callsites_arguments:
                                args = ['ud'] * len(rhs.args)
                                args[var_index] = 'NAC'
                                callsites_arguments[callee] = args
                            else:
                                old_values = callsites_arguments[callee]
                                old_values[var_index] = 'NAC'
                                callsites_arguments[callee] = old_values
                            continue

                        def_stmt = graph.loc_to_ins[def_index]
                        def_stmt_rhs = def_stmt.get_rhs()
                        if type(def_stmt_rhs) is list:
                            continue
                        if not isinstance(def_stmt_rhs, Param):

                            # print("VAR_{}={} in callee {}".format(var,def_stmt_rhs.__str__(), rhs))

                            value = def_stmt_rhs.__str__()
                            if callee not in callsites_arguments:
                                args = ['ud'] * len(rhs.args)
                                if def_stmt_rhs.is_const():
                                    args[var_index] = value
                                else:
                                    args[var_index] = 'NAC'
                                callsites_arguments[callee] = args

                            else:
                                old_values = callsites_arguments[callee]
                                if def_stmt_rhs.is_const():
                                    if old_values[var_index] == 'ud':
                                        old_values[var_index] = value
                                    elif old_values[var_index] != value:
                                        old_values[var_index] = 'NAC'
                                else:
                                    old_values[var_index] = 'NAC'
                                callsites_arguments[callee] = old_values

    def _parse_lib(self, lib_path):
        time_start = datetime.datetime.now()
        try:
            dex_obj = DalvikVMFormat(read(lib_path))
        except ValueError as e:
            print("lib_path: ", lib_path)
            print(e)
            os.remove(lib_path)
            return
        analysis_obj: Analysis = Analysis(dex_obj)
        analysis_obj.create_xref()
        callsites_arguments = self.analysis_callee_arguments_wapper(dex_obj, analysis_obj)
        time_end = datetime.datetime.now()
        decompile_time = time_end - time_start
        self.LOGGER.debug("Decompile complete, time: %d", decompile_time.seconds)

        self.lib_name = os.path.basename(lib_path)
        self.lib_package_name = self._get_lib_name()

        invoke_methodes = set()

        time_start = datetime.datetime.now()
        for cls in dex_obj.get_classes():

            class_name = cls.get_name().replace("/", ".")[1:-1]

            class_name_short = class_name[class_name.rfind(".") + 1:]
            if class_name_short.startswith("R$"):  
                continue

            class_info_list = []
            method_num = 0  # Record the number of methods in the class that are involved in the match
            class_opcode_num = 0  # Record the number of opcodes involved in matching in each class
            class_filter = {}  # Library filters that temporarily record information about each class in a library and merge it into a library filter.
            class_method_md5_list = []
            class_method_info_dict = {}
            class_method_sigs = []
            class_field_sigs = []

            # Get and record the following information about the library class in the Bloom filter: is it an interface, is it an abstract class, is it an enum class, is it a static class, is it a final class, exists a non-Object parent class
            super_class_name = cls.get_superclassname()
            class_access_flags = cls.get_access_flags_string()

            if class_access_flags == "0x0" or class_access_flags == "public":
                class_filter[1] = 1
            elif class_access_flags.find("interface") != -1:
                class_filter[2] = 1
            elif class_access_flags.find("interface") == -1 and class_access_flags.find("abstract") != -1:
                class_filter[3] = 1
            elif class_access_flags.find("enum") != -1:
                class_filter[4] = 1
            elif class_access_flags.find("static") != -1:
                class_filter[5] = 1

            if super_class_name != "Ljava/lang/Object;":
                class_filter[6] = 1

            JAVA_BASIC_TYPR_DICT = {"B": 4, "S": 5, "I": 6, "J": 7, "F": 8, "D": 9, "Z": 10, "C": 11}
            JAVA_BASIC_TYPR_ARR_DICT = {"[B": 13, "[S": 14, "[I": 15, "[J": 16, "[F": 17, "[D": 18, "[Z": 19, "[C": 20}
            RETURN_JAVA_BASIC_TYPR_DICT = {"B": 4, "S": 5, "I": 6, "J": 7, "F": 8, "D": 9, "Z": 10, "C": 11, "V": 12}

            if len(cls.get_fields()) == 0:  
                class_filter[7] = 1
            else:
                for EncodedField_obj in cls.get_fields():
                    a = 1

                    field_access_flag = EncodedField_obj.get_access_flags_string()
                    if 'synthetic' in field_access_flag:
                        continue
                    field_des = EncodedField_obj.get_descriptor()
                    my_field_des = ''

                    if field_access_flag.find("static") == -1:
                        a = 2
                    else:
                        my_field_des = "static "

                    if field_des.startswith("Ljava/lang/Object;"):
                        b = 1
                        my_field_des += "Ljava/lang/Object/;"
                    elif field_des.startswith("Ljava/lang/String;"):
                        b = 2
                        my_field_des += "Ljava/lang/String;"
                    elif field_des.startswith("Ljava/"):
                        b = 3
                        my_field_des += "Ljava/"
                    elif field_des in JAVA_BASIC_TYPR_DICT:
                        b = JAVA_BASIC_TYPR_DICT[field_des]
                        my_field_des += field_des
                    elif field_des.startswith("[Ljava/"):
                        b = 12
                        my_field_des += "[Ljava/"
                    elif field_des in JAVA_BASIC_TYPR_ARR_DICT:
                        b = JAVA_BASIC_TYPR_ARR_DICT[field_des]
                        my_field_des += field_des
                    elif field_des.startswith("["):
                        b = 21
                        my_field_des += "Array"
                    else:
                        b = 22
                        my_field_des += "Other"

                    self._add_class_filter(class_filter, 7 + (a - 1) * 22 + b)
                    # class_field_sigs.append(my_field_des)

            for method in cls.get_methods():

                if method.full_name.find("<init>") != -1 or method.full_name.find("<clinit>") != -1:
                    continue

                method_name = valid_method_name(method.full_name)

                method_descriptor = ""
                method_return_sig = ""
                second_method_descriptor = ""

                method_info = method.get_descriptor()
                method_return_value = method_info[method_info.rfind(")") + 1:]

                if method_return_value.startswith("Ljava/lang/Object"):
                    m = 1
                    method_return_sig = "Ljava/lang/Object/"
                elif method_return_value.startswith("Ljava/lang/String"):
                    m = 2
                    method_return_sig = "Ljava/lang/String/"
                elif method_return_value.startswith("Ljava/"):
                    m = 3
                    method_return_sig = "Ljava/"
                elif method_return_value in RETURN_JAVA_BASIC_TYPR_DICT:
                    m = RETURN_JAVA_BASIC_TYPR_DICT[method_return_value]
                    method_return_sig = method_return_value
                elif method_return_value.startswith("[Ljava/"):
                    m = 13
                    method_return_sig = "\\[Ljava/"
                elif method_return_value in JAVA_BASIC_TYPR_ARR_DICT:
                    m = JAVA_BASIC_TYPR_ARR_DICT[method_return_value] + 1
                    method_return_sig = "\\" + method_return_value
                elif method_return_value.startswith("["):
                    m = 22
                    method_return_sig = "Array"
                else:
                    m = 23
                    method_return_sig = "X"
                method_return_sig = '{(' + method_return_sig + '|V)}'
                method_descriptor = method_return_sig + method_descriptor

                k = 1
                method_access_flags = method.get_access_flags_string()
                if method_access_flags.find("static") == -1:
                    k = 2
                # else:
                #     method_descriptor = "{static}?" + method_descriptor

                if method_access_flags.find("synchronized") != -1:
                    method_descriptor = "({synchronized})?" + method_descriptor

                method_param_info = method_info[method_info.find("(") + 1:method_info.find(")")]
                param_split = method_param_info.split(" ")
                param_len = len(param_split)
                if method_param_info == '':
                    param_len = 0
                parameter_isused_list = self.find_unused_param(method_param_info, method, analysis_obj, param_len)
                parameter_isconstant_list = callsites_arguments.get(method_name, [])
                can_parameter_remove = self.union(parameter_isused_list, parameter_isconstant_list, param_len)
                # can_parameter_remove is a dictionary, key is the position of the parameter, value is whether it can be removed, true means it can be removed, false means it can't be removed

                method_param_info = method_info[method_info.find("(") + 1:method_info.find(")")]
                parm_info = {}
                if method_param_info == "":  
                    n = 1
                else:
                    require_check_for_second_sig = True
                    for i in range(param_len):
                        parm = param_split[i]
                        if parm.startswith("Ljava/"):
                            parm_info[1] = 1
                            append = "{Ljava/}"
                            if parm != 'Ljava/lang/String;':
                                require_check_for_second_sig = False
                        elif parm in ["B", "S", "I", "J", "F", "D", "Z", "C"]:
                            parm_info[2] = 1
                            append = "{" + parm + "}"
                            if parm != 'I':
                                require_check_for_second_sig = False
                        elif parm.startswith("["):
                            parm_info[3] = 1
                            append = "{Array}"
                            require_check_for_second_sig = False
                        else:
                            parm_info[4] = 1
                            append = "{X}"
                            require_check_for_second_sig = False

                        if can_parameter_remove[i]:
                            method_descriptor += '(' + append + ')?'
                        else:
                            method_descriptor += append

                    # Parameters are only int and string, and there are cases where int comes before string, the new signature will be rearranged so that string comes after int.
                    if require_check_for_second_sig:
                        has_int_before_string = any(
                            param_split[i] == "Ljava/lang/String;" and param_split[i + 1] == "I" for i in
                            range(param_len - 1))
                        if has_int_before_string:
                            for i in range(param_len):
                                parm = param_split[i]
                                if parm == "I":
                                    append = "{I}"
                                    if can_parameter_remove[i]:
                                        second_method_descriptor += '(' + append + ')?'
                                    else:
                                        second_method_descriptor += append
                            for i in range(param_len):
                                parm = param_split[i]
                                if parm == "Ljava/lang/String;":
                                    append = "{Ljava/}"
                                    if can_parameter_remove[i]:
                                        second_method_descriptor += '(' + append + ')?'
                                    else:
                                        second_method_descriptor += append
                        second_method_descriptor = method_return_sig + second_method_descriptor

                    if len(parm_info) == 1:
                        if 1 in parm_info:
                            n = 2
                        elif 2 in parm_info:
                            n = 3
                        elif 3 in parm_info:
                            n = 4
                        elif 4 in parm_info:
                            n = 5
                    elif len(parm_info) == 2:
                        if 1 in parm_info and 2 in parm_info:
                            n = 6
                        elif 1 in parm_info and 3 in parm_info:
                            n = 7
                        elif 1 in parm_info and 4 in parm_info:
                            n = 8
                        elif 2 in parm_info and 3 in parm_info:
                            n = 9
                        elif 2 in parm_info and 4 in parm_info:
                            n = 10
                        elif 3 in parm_info and 4 in parm_info:
                            n = 11
                    elif len(parm_info) == 3:
                        if 4 not in parm_info:
                            n = 12
                        elif 3 not in parm_info:
                            n = 13
                        elif 2 not in parm_info:
                            n = 14
                        elif 1 not in parm_info:
                            n = 15
                    else:
                        n = 16

                self._add_class_filter(class_filter, 51 + (k - 1) * 368 + (m - 1) * 16 + n)
                # print("method_descriptor: ", method_descriptor)
                class_method_sigs.append(re.compile('^' + method_descriptor + '$'))
                if second_method_descriptor != '':
                    class_method_sigs.append(re.compile('^' + second_method_descriptor + '$'))

                method_info_list = []
                if method.full_name.startswith("Ljava"):
                    continue

                # bytecode_buff = get_bytecodes_method(dex_obj, analysis_obj, method)
                # method_opcodes = self._get_method_info(bytecode_buff, method_name, invoke_methodes)
                mx: MethodAnalysis = analysis_obj.get_method(method)
                # print(method.name)

                method_opcodes, method_strings, method_size = self.my_get_method_opcodes(mx, method_name,
                                                                                         invoke_methodes)

                # if method_opcodes == "" or len(method_opcodes.split(" ")) > max_opcode_len:
                #     continue


                if len(method_opcodes) == 0 or len(method_opcodes) > 3000:
                    continue

                method_num += 1
                method_opcode_num = len(method_opcodes)
                class_opcode_num += method_opcode_num

                methodmd5 = hashlib.md5()
                methodmd5.update(' '.join(map(str, method_opcodes)).encode("utf-8"))
                method_md5_value = methodmd5.hexdigest()

                class_method_md5_list.append(method_md5_value)

                method_info_list.append(method_md5_value)
                method_info_list.append(method_opcodes)
                method_info_list.append(method_strings)
                method_info_list.append(method_opcode_num)
                method_info_list.append(method_descriptor)
                method_analysis: MethodClassAnalysis = analysis_obj.get_method_analysis(method)
                if method_analysis:
                    method_info_list.append((len(method_analysis.get_xref_from()), method_size))
                if second_method_descriptor != '':
                    method_info_list.append(re.compile(second_method_descriptor))

                class_method_info_dict[method_name] = method_info_list


            # After analyzing all the methods in the class, consider the case where the current class is an interface or an abstract class
            if (class_access_flags.find("interface") != -1 or class_access_flags.find("abstract") != -1) \
                    and len(class_method_info_dict) == 0:  
                class_info_list = [len(cls.get_methods()), class_filter]
                self.classes_dict[cls.get_name().replace("/", ".")[1:-1]] = class_info_list
                # Methods in interfaces or abstract classes are also counted in lib_method_num, lib_opcode_num
                self.lib_method_num += len(cls.get_methods())
                self.lib_opcode_num += (len(cls.get_methods()) * abstract_method_weight)
                continue

            if len(class_method_info_dict) == 0:
                continue

            self.interface_lib = False

            self.lib_opcode_num += class_opcode_num

            class_method_md5_list.sort()
            class_md5 = ""
            for method_md5 in class_method_md5_list:
                class_md5 += method_md5

            classmd5 = hashlib.md5()
            classmd5.update(class_md5.encode("utf-8"))
            class_md5_value = classmd5.hexdigest()

            class_info_list.append(class_md5_value)
            class_info_list.append(method_num)
            class_info_list.append(class_opcode_num)
            class_info_list.append(class_filter)
            class_info_list.append(class_method_info_dict)
            # class_info_list.append(Counter(class_field_sigs))
            class_info_list.append(class_method_sigs)
            self.classes_dict[cls.get_name().replace("/", ".")[1:-1]] = class_info_list

            self.lib_method_num += method_num


        time_end = datetime.datetime.now()
        extract_info_time = time_end - time_start
        self.LOGGER.debug("Parsing library completed, time: %d", extract_info_time.seconds)

    def _get_lib_name(self):
        lib = self.lib_name
        lib_name_version = lib[:lib.rfind("-")]
        return lib_name_version

    def my_get_method_opcodes(self, mx: MethodAnalysis, method_name: str,
                              invoke_methodes: set):
        strings = set()
        method_size = 0
        instructions = []
        cur_instructions = []
        num = 1
        queue = []
        visited = set()
        try:
            if len(mx.basic_blocks.bb) > 0:
                first_block: DVMBasicBlock = mx.basic_blocks.get_basic_block_pos(0)
                queue.append(first_block)  
                if len(mx.exceptions.gets()) > 0:
                    for exception in mx.exceptions.gets():
                        for exc in exception.exceptions:
                            queue.append(exc[2])
            else:
                return instructions, strings, -1
        except Exception as e:
            print(e)
            return instructions, strings, -1

        while queue:
            block = queue.pop(0)  
            if block in visited:
                continue
            visited.add(block)

            for ins in block.get_instructions():
                name = ins.get_name()
                ins_size = instruction_size_map.get(name)
                if ins_size:
                    method_size += ins_size
                instructions.append(ins.get_op_value())
                cur_instructions.append(ins.get_op_value())
                if name.startswith("invoke"):
                    line = ins.get_output()
                    invoke_info = line[line.find("L"):]
                    method_info = invoke_info.replace("->", " ").replace("(", " (")

                    if method_info.startswith("Ljava"):
                        continue

                    node_info = [cur_instructions]
                    invoke_method_valid_name = valid_method_name(method_info)  
                    invoke_methodes.add(invoke_method_valid_name)
                    node_info.append(invoke_method_valid_name)
                    self.nodes_dict[method_name + "_" + str(num)] = node_info
                    num += 1
                    cur_instructions = []
                elif name == "const-string":
                    raw_string = ins.get_raw_string()
                    if raw_string != "":
                        strings.add(raw_string)

            last_ins = list(block.get_instructions())[-1]
            if last_ins.get_name() in self.condition_jump_ins and len(block.get_next()) == 2:  
                blocks = block.get_next()
                false_target = block.get_end()
                true_branch = None
                false_branch = None
                if false_target == blocks[0][2].get_start():
                    true_branch = blocks[1][2]
                    false_branch = blocks[0][2]
                elif false_target == blocks[1][2].get_start():
                    true_branch = blocks[0][2]
                    false_branch = blocks[1][2]
                else:
                    Exception("Invalid jump target offset")

                if last_ins.get_name() in self.half_condition_jump_ins:
                    queue.append(true_branch)
                    queue.append(false_branch)
                else:
                    queue.append(false_branch)
                    queue.append(true_branch)

            else:
                # If the last instruction is not a conditional jump, add all subblocks to the queue
                for child in block.get_next():
                    queue.append(child[2])

        node_info = [cur_instructions, []]
        self.nodes_dict[method_name + "_" + str(num)] = node_info
        return instructions, strings, method_size


    def _add_class_filter(self, class_filter, index):
        index_num = class_filter.get(index, 0)
        count = index_num + 1
        if count > filter_record_limit:
            count = filter_record_limit
        class_filter[index] = count

    def find_unused_param(self, method_param_info, method, analysis_obj, param_len):
        if param_len == 0:
            return []
        parameter_dict = dict()
        parameter_noexist = [True] * param_len
        if method.code == None:
            return parameter_noexist
        parameter_num = method.code.get_registers_size()
        start_num = parameter_num - len(method_param_info.split(" "))
        for i in range(param_len):
            parameter_dict['v' + str(start_num)] = i
            start_num += 1
        mx = analysis_obj.get_method(method)
        basic_blocks = mx.basic_blocks.gets()
        idx = 0
        for bb in basic_blocks:
            for ins in bb.get_instructions():
                ops = ins.get_output().split(" ")
                for op in ops:
                    op = op.strip(",")
                    if op in parameter_dict:
                        parameter_noexist[parameter_dict[op]] = False
            # idx += ins.get_length()
        return parameter_noexist

    def union(self, list1, list2, param_num):
        if list2 == []:
            return list1
        result = {}
        if param_num == 0:
            return result
        for i in range(param_num):
            if list1[i] == True or list2[i].startswith("CST"):
                result[i] = True
            else:
                result[i] = False

        return result
