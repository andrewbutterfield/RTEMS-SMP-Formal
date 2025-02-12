# SPDX-License-Identifier: BSD-2-Clause
"""Refines Annotated SPIN output to test program code"""

# Copyright (C) 2019-2023 Trinity College Dublin (www.tcd.ie)
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions
# are met:
# 1. Redistributions of source code must retain the above copyright
#    notice, this list of conditions and the following disclaimer.
# 2. Redistributions in binary form must reproduce the above copyright
#    notice, this list of conditions and the following disclaimer in the
#    documentation and/or other materials provided with the distribution.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
# ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
# LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
# CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
# SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
# INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
# CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
# ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
# POSSIBILITY OF SUCH DAMAGE.

import itertools
import logging
import yaml
from pathlib import Path

logger = logging.getLogger (__name__)

class command:

    def __init__(self, ref_dict
                 , outputLOG = False
                 , annoteComments = True
                 , outputSWITCH = True
                 ):
        self.ref_dict = ref_dict
        self.ref_dict_keys = ref_dict.keys()

        self.inSTRUCT = False  # True when in STRUCT
        self.inSEQ = False  # True when in SEQ
        self.seqForSEQ = "" # Holds space-separated sequence output string when in SEQ
        self.inName = ""     # Set to SEQ/STRUCT name when inside

        self.testName = "Un-named Test"
        self.defCode = []     # list of strings
        self.declCode = []    # list of strings
        self.testCodes = []   # list (indexed by pid) of list of strings
        self.procIds = set()  # set of process ids in use
        self.currentId = 0    # currently running process
        self.switchNo = 0

        # Use c by default if language not set
        self.setComments("c")
        self.setDefaults("c")

        self.outputLOG = outputLOG
        self.annoteComments = annoteComments
        self.outputSWITCH = outputSWITCH

    def setComments(self, language):
        logger.debug(f"Set LANGUAGE to {language} (comments)\n")
        language_file = Path(Path(__file__).parent.absolute() /
                             f"languages/{language}.yml")
        if language_file.exists():
            with open(language_file) as f:
                language_yaml = yaml.load(f, Loader=yaml.FullLoader)
                comment_keys = {"EOLC", "CMTBEGIN", "CMTEND"}
                for key in comment_keys:
                    if key not in language_yaml.keys():
                        logger.error(f"{key} not set in {language}.yml")
                        raise SystemExit()
                    else:
                        setattr(self, key, language_yaml[key])
        elif language != "c":
            logger.debug(f"Unknown LANGUAGE {language}, set to C\n")
            self.setComments("c")
        else:
            logger.error(f"Ensure language file for {language} is present "
                         f"before generating tests (comments)\n")
            logger.error(f"File {language_file} not found\n")
            raise SystemExit()

    def setDefaults(self, language):
        logger.debug(f"Set LANGUAGE to {language} (non-comment defaults)\n")
        language_file = Path(Path(__file__).parent.absolute() /
                             f"languages/{language}.yml")
        if language_file.exists():
            with open(language_file) as f:
                language_yaml = yaml.load(f, Loader=yaml.FullLoader)
                comment_keys = {"EOLC", "CMTBEGIN", "CMTEND"}
                for key in language_yaml.keys() - comment_keys:
                    setattr(self, key, language_yaml[key])
        elif language.lower() != "c":
            logger.debug(f"Unknown LANGUAGE {language}, set to C\n")
            self.setDefaults("c")
        else:
            logger.error(f"Ensure language file for {language} is present "
                         f"before generating tests (non-comment defaults)\n")
            logger.error(f"File {language_file} not found\n")
            raise SystemExit()

    def setupSegmentCode(self):
        if 'SEGNAMEPFX' in self.ref_dict_keys:
            self.SEGNAMEPFX = self.ref_dict['SEGNAMEPFX']
        else:
            logger.debug("SEGNAMEPFX not defined, using "+self.SEGNAMEPFX)
        if 'SEGARG' in self.ref_dict_keys:
            self.SEGARG = self.ref_dict['SEGARG']
        else:
            logger.debug("SEGARG not defined, using "+self.SEGARG)
        if 'SEGDECL' in self.ref_dict_keys:
            self.SEGDECL  = self.ref_dict['SEGDECL']
        else:
            logger.debug("SEGDECL not defined, using "+self.SEGDECL)
        if 'SEGBEGIN' in self.ref_dict_keys:
            self.SEGBEGIN = self.ref_dict['SEGBEGIN']
        else:
            logger.debug("SEGBEGIN not defined, using "+self.SEGBEGIN)
        if 'SEGEND' in self.ref_dict_keys:
            self.SEGEND = self.ref_dict['SEGEND']
        else:
            logger.debug("SEGEND not defined, using "+self.SEGEND)
        logger.debug("SEGNAMEPFX is '"+self.SEGNAMEPFX+"'")
        logger.debug("SEGARG is '"+self.SEGARG+"'")
        logger.debug("SEGDECL is '"+self.SEGDECL+"'")
        logger.debug("SEGBEGIN is '"+self.SEGBEGIN+"'")
        logger.debug("SEGEND is '"+self.SEGEND+"'")

    def setupLanguage(self):
        if 'LANGUAGE' in self.ref_dict_keys:
            language = self.ref_dict['LANGUAGE']
            self.setComments(language.lower())
            self.setDefaults(language.lower())
            self.setupSegmentCode()
        else:
            pass  # assume default: C

    def collectPIds(self, ln):
        if len(ln) > 0:
            self.procIds.add(int(ln[0]))

    def addCode(self, id, codelines):
        # logger.debug("addCode lines are {} {}".format(type(codelines),codelines))
        self.testCodes = self.testCodes + [(int(id), codelines)]

    def addCode_int(self, pid, f_codelines0, f_codelines1, value):
        if value.isdigit():
            if value == "0":
                self.addCode(pid, [f_codelines0])
            else:
                self.addCode(pid, [f_codelines1])

    def switchIfRequired(self, ln):
        if len(ln) > 0:
            pid = ln[0]
            i = int(pid)
            if i == self.currentId:
                pass
            else: # proc self.currentId stops here, and proc i resumes
                self.switchNo =self.switchNo+1
                if 'SUSPEND' not in self.ref_dict_keys:
                    self.addCode(pid,[self.EOLC+" SUSPEND: no refinement entry found"])
                else:
                    code = self.ref_dict['SUSPEND']
                    self.addCode(self.currentId,[code.format(self.switchNo,self.currentId,i)])
                if 'WAKEUP' not in self.ref_dict_keys:
                    self.addCode(pid,[self.EOLC+" WAKEUP: no refinement entry found"])
                else:
                    code = self.ref_dict['WAKEUP']
                    self.addCode(i,[code.format(self.switchNo,i,self.currentId)])
                self.currentId = i

    def logSPINLine(self, ln):
        if len(ln) > 1:
            pid = int(ln[0])
            str = ' '.join(ln)
            if ln[1] in ['NAME','DEF']:
                self.defCode = self.defCode + [self.EOLC+" @@@ {}".format(str)]
            elif ln[1] in ['DECL','DCLARRAY'] :
                if pid == 0:
                    self.declCode = ( self.declCode 
                                      + [self.EOLC+" @@@ {}".format(str)] )
                else:
                    self.addCode(pid,[self.EOLC+" @@@ {}".format(str)])
            elif ln[1] == 'LOG' :
                pass
            else:
                self.addCode(pid,['T_log(T_NORMAL,"@@@ {}");'.format(str)])

    # Promela Annotations
    #
    # Format: `@@@ <pid> <KEYWORD> <thing1> ... <thingN>` where N >= 0
    #
    # Things:
    #  <pid>  Promela Process Id of proctype generating annotation
    #  <word> chunk of text containing no white space
    #  <name> Promela variable/structure/constant identifier
    #  <type> Promela type identifier
    #  <tid>  OS Task/Thread/Process Id alias
    #  [ <thing> ]  An optional <thing>
    #  ( <thing1> | <thing2>) A choice of <thing1> or <thing2>
    #  _  unused argument (within containers)
    #
    # KEYWORDS and "things"
    # LOG <word1> ... <wordN>
    # NAME <name>
    # INIT
    # DEF <name> <value>
    # DECL <type> <name> [<value>]
    # DCLARRAY <type> <name> <value>
    # TASK <name>
    # SIGNAL <name> <value>
    # WAIT   <name> <value>
    # STATE tid <name>
    # SCALAR (<name>|_) [<index>] <value>
    # PTR <name> <value>
    # STRUCT <name>
    # SEQ <name>
    # END <name>
    # CALL <name> <value1> ... <valueN>

    # Refinement Mechanisms
    #   Direct Output - no lookup
    #   Keyword Refinement - lookup (the) <KEYWORD>
    #   Name Refinement - lookup (first) name
    #    The same name may appear in different contexts
    #    We add '_XXX' suffixes to lookup less frequent uses
    #     _DCL - A variable declaration
    #     _PTR - The pointer value itself
    #     _FSCALAR - A scalar that is a struct field
    #     _FPTR - A pointer that is a struct field
    #   Type Refinement - lookup (first) type
    #   Typed-Name Refinement - lookup type-name

    # LOG <word1> ... <wordN>
    #  Direct Output


    def refineSPINLine(self, spin_line):
        match spin_line:
            # NAME <name>
            #  Keyword Refinement (NAME)
            case [pid, 'LOG', *rest]:
                if self.outputLOG:
                    ln = ' '.join(rest)
                    self.addCode(pid, ["T_log(T_NORMAL,{});".format(ln)])
                else:
                    pass
            case [pid, "NAME", name]:
                if 'NAME' not in self.ref_dict_keys:
                    self.addCode(pid, [self.EOLC+" CANNOT REFINE 'NAME'"])
                else:
                    self.addCode(pid, self.ref_dict["NAME"].rsplit('\n'))
            # INIT
            #   Keyword Refinement (INIT)
            case [pid, "INIT"]:
                if 'INIT' not in self.ref_dict_keys:
                    self.addCode(pid, [self.EOLC+" CANNOT REFINE 'INIT'"])
                else:
                    self.addCode(pid, self.ref_dict["INIT"].rsplit('\n'))
            # TASK <name>
            #  Name Refinement (<name>)
            case [pid, "TASK", task_name]: 
                if task_name not in self.ref_dict_keys:
                    self.addCode(pid, [self.EOLC+" CANNOT REFINE TASK {}".format(task_name)])
                else:
                    self.addCode(pid, self.ref_dict[task_name].rsplit('\n'))
            # SIGNAL <value>
            #   Keyword Refinement (SIGNAL)
            case [pid,'SIGNAL',value]:
                if 'SIGNAL' not in self.ref_dict_keys:
                    self.addCode(pid, [self.EOLC+" CANNOT REFINE SIGNAL {}".format(value)])
                else:
                    self.addCode(pid, self.ref_dict['SIGNAL'].format(value).rsplit('\n'))
            # WAIT <value>
            #   Keyword Refinement (WAIT)
            case [pid,'WAIT',value]:
                if 'WAIT' not in self.ref_dict_keys:
                    self.addCode(pid, [self.EOLC+" CANNOT REFINE WAIT {}".format(value)])
                else:
                    self.addCode(pid, self.ref_dict['WAIT'].format(value).rsplit('\n'))
            # DEF <name> <value>
            #   Direct Output
            case [pid,'DEF',name,value]:
                self.defCode = self.defCode + [' '.join(['#define',name,value])]
            # DECL <type> <name> [<value>]
            #   Name Refinement (<name>_DCL)
            #   add with 'static' to declCode if pid==0,
            #   add without 'static' using addCode, otherwise
            case [pid, 'DECL', typ, name, *rest]:
                logger.debug("Processing DECL {} {} {}".format(type,name,rest))
                name_dcl = name + '_DCL'
                if name_dcl not in self.ref_dict_keys:
                    decl = self.EOLC+" CANNOT REFINE Decl {}".format(name_dcl)
                else:
                    decl = ' '.join([self.ref_dict[name_dcl],name])
                if len(rest) > 0:
                    decl = decl + " = " + rest[0] + ";"
                else:
                    decl = decl + ";"
                if int(pid) == 0:
                    decl = 'static ' + decl
                    self.declCode = self.declCode + [decl]
                else:
                    self.addCode(pid,[decl])
            # DCLARRAY <type> <name> <value>
            #   Name Refinement (<name>_DCL)
            #   add with 'static' to declCode if pid==0,
            #   add without 'static' using addCode, otherwise
            case [pid, 'DCLARRAY', typ, name, value]:
                logger.debug("Processing DECLARRAY {} {} {}".format(type, name, value))
                name_dcl = name + '_DCL'
                if name_dcl not in self.ref_dict_keys:
                    dclarray = [self.EOLC+" DCLARRAY: no refinement entry for '{}'".format(name_dcl)]
                else:
                    code = self.ref_dict[name_dcl].format(name, value)
                    if int(pid) == 0:
                        code = 'static ' + code
                    dclarray = code.rsplit('\n')
                if int(pid) == 0:
                    self.declCode = self.declCode + dclarray
                else:
                    self.addCode(pid,dclarray)
            # PTR <name> <value>
            #   Name (_PTR/_FPTR) refinement
            case [pid, 'PTR', name, value]:
                i = int(pid)
                if not self.inSTRUCT:
                    pname = name + '_PTR'
                    if pname not in self.ref_dict_keys:
                        self.addCode(pid, [self.EOLC+" PTR: no refinement entry for '{}'".format(pname)])
                    else:
                        pcode = self.ref_dict[pname].rsplit('\n')
                        self.addCode_int(pid, pcode[0], pcode[1].format(value), value)
                else:
                    pname = name + '_FPTR'
                    if pname not in self.ref_dict_keys:
                        self.addCode(pid, [self.EOLC+" PTR(field): no refinement for '{}'".format(pname)])
                    else:
                        pcode = self.ref_dict[pname].rsplit('\n')
                        self.addCode_int(pid, pcode[0], pcode[1].format(self.inName, value), value)
            # CALL <name> <value0> .. <valueN>
            # Name refinement
            case [pid,'CALL',name,*rest]:
                logger.debug("Processing CALL {} {}".format(name,rest))
                if name not in self.ref_dict_keys:
                    logger.debug("CALL name not found")
                    self.addCode(pid, [self.EOLC+" CALL: no refinement entry for '{}'".format(name)])
                else:
                    code = self.ref_dict[name]
                    logger.debug("CALL code: {}".format(code))
                    match len(rest):
                        case 0: callcode = code.rsplit('\n')
                        case 1: callcode = (code.format(rest[0])).rsplit('\n')
                        case 2: callcode = (code.format(rest[0],rest[1])).rsplit('\n')
                        case 3: callcode = (code.format(rest[0],rest[1],rest[2])).rsplit('\n')
                        case 4: callcode = (code.format(rest[0],rest[1]
                                               ,rest[2],rest[3])).rsplit('\n')
                        case 5: callcode = (code.format(rest[0],rest[1]
                                               ,rest[2],rest[3],rest[4])).rsplit('\n')
                        case 6: callcode = (code.format(rest[0],rest[1]
                                               ,rest[2],rest[3],rest[4],rest[5])).rsplit('\n')
                        case _: callcode = [self.EOLC+" CALL: can't handle > 6 arguments"]
                    self.addCode(pid,callcode)
                logger.debug("CALL complete")
            case [pid,'STRUCT',name]:
                self.inSTRUCT = True # should check not already inside anything!
                self.inName = name
            # SEQ <name>
            case [pid,'SEQ',name]:
                self.inSEQ = True # should check not already inside anything!
                self.seqForSEQ = ""
                self.inName = name
            # END <name>
            case [pid,'END',name]:
                if self.inSTRUCT:
                    self.inSTRUCT = False
                if self.inSEQ:
                    seqName = name + "_SEQ"
                    if seqName not in self.ref_dict_keys:
                        self.addCode(pid,["SEQ END: no refinement for ".format(seqName)])
                    else:
                        codelines = self.ref_dict[seqName].rsplit('\n')
                        for code in codelines:
                            self.addCode(pid,[code.format(self.seqForSEQ)])
                    self.inSEQ = False
                    self.seqForSEQ = ""
                self.inName = ""
            # SCALAR _ <value>
            case [pid,'SCALAR','_',value]:
                # should only be used inside SEQ
                self.seqForSEQ = self.seqForSEQ + " " + value
            # SCALAR <name/field> <value>
            # Name (<name>/_FSCALAR) Refinement
            case [pid,'SCALAR',name,value]:
                # should not be used inside SEQ
                if not self.inSTRUCT:
                    if name not in self.ref_dict_keys:
                        self.addCode(pid,[self.EOLC+" SCALAR: no refinement entry for '{}'".format(name)])
                    else:
                        code = self.ref_dict[name]
                        self.addCode(pid,(code.format(value)).rsplit('\n'))
                else:
                    field = name + "_FSCALAR"
                    if field not in self.ref_dict_keys:
                        self.addCode(pid,[self.EOLC+" SCALAR(field): no refinement entry for '{}'".format(field)])
                    else:
                        code = self.ref_dict[field]
                        self.addCode(pid,[code.format(self.inName,value)])
            # SCALAR <name> <index> <value>
            # Name (<name>/_FSCALAR) Refinement
            case [pid,'SCALAR',name,index,value]:
                # should not be used inside SEQ
                if not self.inSTRUCT:
                    if name not in self.ref_dict_keys:
                        self.addCode(pid,[self.EOLC+" SCALAR-3: no refinement entry for '{}'".format(name)])
                    else:
                        code = self.ref_dict[name]
                        self.addCode(pid,code.format(index,value).rsplit('\n'))
                else:
                    field = name + "_FSCALAR"
                    if field not in self.ref_dict_keys:
                        self.addCode(pid,[self.EOLC + " SCALAR(field): no refinement entry for '{}'".format(field)])
                    else:
                        code = self.ref_dict[field]
                        self.addCode(pid,[code.format(self.inName,value)])
            # STATE <tid> <name>
            # Name Refinement
            case [pid, 'STATE', tid, state]:
                if state not in self.ref_dict_keys:
                    self.addCode(pid,[self.EOLC+" STATE: no refinement entry for '{}'".format(state)])
                else:
                    code = self.ref_dict[state]
                    self.addCode(pid,[code.format(tid)])
            # catch-all for refineSPINLine
            case [pid, hd, *rest]:
                dunno = self.EOLC+"  DON'T KNOW HOW TO REFINE: "+pid+" '"+str(hd)
                self.addCode(pid, [dunno])
            # catch-all for refineSPINLine
            case [pid]:
                dunno = self.EOLC+"  DON'T KNOW HOW TO REFINE: "+pid
                self.addCode(pid, [dunno])
            # catch-all for refineSPINLine
            case _:
                pass

    def refineSPINLine_main(self, ln):
        self.collectPIds(ln)
        if self.outputSWITCH:
            self.switchIfRequired(ln)
        else:
            pass
        if self.annoteComments:
            self.logSPINLine(ln)
        else:
            pass
        self.refineSPINLine(ln)

    def test_body (self):
        yield "\n"
        yield self.EOLC+"  ===============================================\n\n"



        for line in self.defCode:
            yield line+"\n"


        for line in self.declCode:
            yield line+"\n"

        # def testseg_name (segno): return "TestSegment{}".format(segno)
        def get_id (id_codes): return id_codes[0]

        for sno, lines in itertools.groupby (sorted (self.testCodes, key = get_id), get_id):
            yield "\n"
            yield self.EOLC+"  ===== TEST CODE SEGMENT {} =====\n\n".format(sno)
            testseg_name = self.SEGNAMEPFX.format(sno)
            testseg = (self.SEGDECL).format(testseg_name,self.SEGARG)
            yield "{}{}\n".format(testseg, self.SEGBEGIN)

            for lines0 in lines:
                for line in lines0[1]:
                    yield "  "+line+"\n"

            yield self.SEGEND+"\n"

        yield "\n"
        yield self.EOLC+"  ===============================================\n\n"
