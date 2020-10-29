# This is an options module that is used by the lemma synthesis source code.
# TODO: move the material here into a config file format with library support, say json or toml

import os
import importlib_resources

###############################################################################
# Setting lemma synthesis options here. DO NOT MODIFY.
# DO NOT switch on prefetching. Code is not updated to handle current sygus output.
experimental_prefetching_switch = 'off'
exclude_set_type_definitions_switch = 'off'
###############################################################################

log_file_path = os.path.abspath(importlib_resources.files('lemsynth')/'../logs')

