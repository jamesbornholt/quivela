# Copyright 2018 Amazon.com, Inc. or its affiliates. All Rights Reserved.
# 
# Licensed under the Apache License, Version 2.0 (the "License").
# You may not use this file except in compliance with the License.
# A copy of the License is located at
# 
#     http://www.apache.org/licenses/LICENSE-2.0
# 
# or in the "license" file accompanying this file. This file is distributed 
# on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either 
# express or implied. See the License for the specific language governing 
# permissions and limitations under the License.

import collections
import os
import re
from string import Template as Snippet
from typing import Dict, List, Optional, Set


class Template(object):
    def __init__(self, name: str) -> None:
        path = os.path.join(os.path.dirname(__file__), name)
        with open(path) as f:
            self.snippets = self._parse(f.read())
    
    def _parse(self, tmpl: str) -> Dict[str, Snippet]:
        state = None  # type: Optional[str]
        snips = {}  # type: Dict[str, Snippet]
        snip = ""
        keys = set()  # type: Set[str]
        for l in tmpl.split("\n"):
            if l.startswith("////"):
                continue
            elif l.startswith("///<"):
                m = re.match("///< (START|END) (\w+)", l)
                if not m:
                    raise Exception("unrecognized delimiter {}".format(l))
                if m.group(1) == "START":
                    assert state is None
                    state = m.group(2)
                elif m.group(1) == "END":
                    assert state == m.group(2)
                    snips[state] = Snippet(snip)
                    state = None
                    snip = ""
                    keys = set()
            elif state is not None:
                if snip != "":
                    snip += "\n"
                snip += l
        assert state is None
        return snips
    
    def get(self, k: str) -> Snippet:
        if k not in self.snippets:
            raise Exception("unknown snippet {}".format(k))
        return self.snippets[k]

equivalence = Template("equivalence_template.dfy")
