class VariableNamer(object):
    """Variable Name Generator."""

    def __init__(self, base_name, separator="_", counter=0):
        self._base_name = base_name
        self._counter_init = counter
        self._counter_curr = counter
        self._separator = separator

    def get_init(self):
        """Return initial name.
        """
        suffix = self._separator + "%s" % str(self._counter_init)

        return self._base_name + suffix

    def get_current(self):
        """Return current name.
        """
        suffix = self._separator + "%s" % str(self._counter_curr)

        return self._base_name + suffix

    def get_next(self):
        """Return next name.
        """
        self._counter_curr += 1

        suffix = self._separator + "%s" % str(self._counter_curr)

        return self._base_name + suffix

    def reset(self):
        """Restart name counter.
        """
        self._counter_curr = self._counter_init
