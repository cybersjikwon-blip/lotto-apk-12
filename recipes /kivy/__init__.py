import os

import pythonforandroid.recipes.kivy as _upstream
from pythonforandroid.recipes.kivy import KivyRecipe


class KivyLeanRecipe(KivyRecipe):
    python_depends = ['certifi', 'chardet', 'idna', 'six', 'urllib3',
                      'filetype']

    def get_recipe_dir(self):
        return os.path.dirname(_upstream.__file__)


recipe = KivyLeanRecipe()
