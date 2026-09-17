[app]

title = 흥보lotto대박
package.name = heungbo
package.domain = org.heungbo

source.dir = .
source.include_exts = py,png,jpg,ttf,otf,json,xml

version = 1.2

requirements = python3,kivy==2.3.1,plyer,certifi,pillow,camera4kivy,gestures4kivy,libzbar,pyzbar

icon.filename = icon.png
presplash.filename = presplash.png
android.presplash_color = #131519

orientation = portrait
fullscreen = 0

android.permissions = INTERNET,ACCESS_NETWORK_STATE,ACCESS_COARSE_LOCATION,ACCESS_FINE_LOCATION,CAMERA,POST_NOTIFICATIONS

android.api = 34
android.minapi = 24
android.ndk_api = 24
android.archs = arm64-v8a
android.allow_backup = True
android.enable_androidx = True
android.accept_sdk_license = True
android.wakelock = False

p4a.branch = v2026.05.09
p4a.local_recipes = ./recipes

# camera4kivy 의 Java 카메라 제공자를 APK 에 넣는다.
# 이 훅이 androidx 설정과 camerax gradle 의존성을 자동으로 넣어주므로
# android.gradle_dependencies 는 직접 쓰지 않는다.
p4a.hook = camerax_provider/gradle_options.py

[buildozer]
log_level = 2
warn_on_root = 0
