# Copyright (c) 2014, Fundacion Dr. Manuel Sadosky
# All rights reserved.

# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:

# 1. Redistributions of source code must retain the above copyright notice, this
# list of conditions and the following disclaimer.

# 2. Redistributions in binary form must reproduce the above copyright notice,
# this list of conditions and the following disclaimer in the documentation
# and/or other materials provided with the distribution.

# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

from __future__ import absolute_import

from .helpers import *

from .arithmetic import dispatcher as arithmetic_dispatcher
from .bitwise import dispatcher as bitwise_dispatcher
from .control import dispatcher as control_dispatcher
from .flag import dispatcher as flag_dispatcher
from .logical import dispatcher as logical_dispatcher
from .misc import dispatcher as misc_dispatcher
from .sse import dispatcher as sse_dispatcher
from .string import dispatcher as string_dispatcher
from .transfer import dispatcher as transfer_dispatcher

dispatcher = {}
dispatcher.update(arithmetic_dispatcher)
dispatcher.update(bitwise_dispatcher)
dispatcher.update(control_dispatcher)
dispatcher.update(flag_dispatcher)
dispatcher.update(logical_dispatcher)
dispatcher.update(misc_dispatcher)
dispatcher.update(sse_dispatcher)
dispatcher.update(string_dispatcher)
dispatcher.update(transfer_dispatcher)
