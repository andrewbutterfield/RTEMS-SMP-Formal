##############################################################################
# FV2-201
#
# Copyright (C) 2019-2021 Trinity College Dublin (www.tcd.ie)
#
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are
# met:
#
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#
#     * Redistributions in binary form must reproduce the above
#       copyright notice, this list of conditions and the following
#       disclaimer in the documentation and/or other materials provided
#       with the distribution.
#
#     * Neither the name of the copyright holders nor the names of its
#       contributors may be used to endorse or promote products derived
#       from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
# "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
# LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
# A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
# OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
# SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
# LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
# DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
# THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
##############################################################################
print("\n\tSpec2Tex \n")

import argparse
import yaml

def lines(string): return string.rsplit('\n')

def words(string): return string.rsplit(' ')

def wordlines(string): return fmap (words,lines(string))

def texEsc(string): return string.replace( "_", "\\_" )

latexNewLine = "\n\\newline\n"
latexPageBreak = "\n\\newpage\n"

def latexHeader(kind,content):
    return ( "\n\n\\"+kind+"{"+content+"}\n\n" )



# Main Program from here

claparser = argparse.ArgumentParser(description="YAML Spec to LaTeX")
claparser.add_argument("root", help="Spec filename root")

cl_args = claparser.parse_args()
fileRoot = cl_args.root

specFile = fileRoot + ".yml"
texFile  = fileRoot + ".tex"

# The following should be configurable

texHdr = "section"
preHdr = "subsection"
postHdr = "subsection"
skipHdr = "subsection"
mapHdr = "subsection"
transHdr = "subsubsection"


print("Converting {0} to {1}\n".format(specFile,texFile))

with open(specFile) as specfile:
   spec = specfile.read()
   spec_dict = yaml.safe_load(spec)

texfile = open(texFile,'w')

texfile.write(latexHeader(texHdr,"Specification \\texttt{"+fileRoot+"}"))

print("\nOutputting Pre-conditions")
preconds = spec_dict["pre-conditions"]
print("Found {} pre-conditions".format(len(preconds)))

texfile.write(latexHeader(preHdr,"Pre-Conditions"))

texfile.write("\\begin{description}")
for pcentry in preconds:
    nm = pcentry["name"]
    print("  '{}'".format(nm))
    texfile.write("\n  \\item[{}]~".format(nm))
    sts = pcentry["states"]
    texfile.write("\n  \\begin{description}")
    for st in sts:
        stnm = st["name"]
        # print("    '{}'".format(stnm))
        texfile.write("\n  \\item[{}]".format(stnm))
        txt = texEsc(st["text"].rstrip('\n'))
        # print('    "{}"'.format(txt.rstrip('\n')))
        texfile.write("\n    {}".format(txt))
        code = st["test-code"]
        texfile.write("\n\\begin{verbatim}\n")
        texfile.write(code)
        texfile.write("\\end{verbatim}")
    texfile.write("\n  \\end{description}\n")
texfile.write("\n\\end{description}\n")

print("\nOutputting Post-conditions")
postconds = spec_dict["post-conditions"]
print("Found {} post-conditions".format(len(postconds)))

texfile.write(latexHeader(postHdr,"Post-Conditions"))

texfile.write("\\begin{description}")
for pcentry in postconds:
    nm = pcentry["name"]
    print("  '{}'".format(nm))
    texfile.write("\n  \\item[{}]~".format(nm))
    sts = pcentry["states"]
    texfile.write("\n  \\begin{description}")
    for st in sts:
        stnm = st["name"]
        # print("    '{}'".format(stnm))
        texfile.write("\n  \\item[{}]".format(stnm))
        txt = texEsc(st["text"].rstrip('\n'))
        # print('    "{}"'.format(txt.rstrip('\n')))
        texfile.write("\n    {}".format(txt))
        code = st["test-code"]
        texfile.write("\n\\begin{verbatim}\n")
        texfile.write(code)
        texfile.write("\\end{verbatim}")
    texfile.write("\n  \\end{description}\n")
texfile.write("\n\\end{description}\n")

print("\nOutputting Skip Reasons")
skipR = spec_dict["skip-reasons"]

texfile.write(latexHeader(skipHdr,"Skip Reasons"))

texfile.write("\\begin{description}")
for skip in skipR.keys():
    reason = texEsc(skipR[skip].rstrip('\n'))
    print("  {}".format(skip))
    texfile.write("\n  \\item[{}]~".format(skip))
    # print('  "{}"'.format(reason.rstrip('\n')))
    texfile.write("\n    {}".format(reason))
texfile.write("\n\\end{description}\n")

print("\nOutputting Transition Map")
transmap = spec_dict["transition-map"]
print("Found {} transition mappings".format(len(transmap)))

texfile.write(latexPageBreak)
texfile.write(latexHeader(mapHdr,"Transition Maps"))

tix = 1
for tmap in transmap:
    print("Transition",tix)
    texfile.write(latexHeader(transHdr,"Transition {}".format(tix)))
    tix=tix+1
    # print("PRE:")
    texfile.write("\n\\textsc{Before:}")
    pre = tmap["pre-conditions"]
    for preid in pre.keys():
        preval = pre[preid]
        # print("  ",preid,preval)
        if type(preval) == str:
            if preval != "N/A":
                texfile.write("\n\\newline.~~~~${}={}$".format(preid,preval))
        else:
            if len(preval) == 1:
                texfile.write("\n\\newline.~~~~${}={}$".format(preid,preval[0]))
            if len(preval) > 1:
                texfile.write("\n\\newline.~~~~${} \in ".format(preid))
                prevals = ','.join(preval)
                texfile.write("\\{"+prevals+"\\}$")

    # print("POST:")
    texfile.write("\n\\newline\\textsc{After:}")
    post = tmap["post-conditions"]
    if type(post) is str:
        texfile.write("\n\\newline~{}".format(post))
        # print("  ",post)
    else:
        for postid in post.keys():
            postval = post[postid]
            # print("  ",postid,postval)
            texfile.write("\n\\newline.~~~~{}={}".format(postid,postval))

texfile.close()
