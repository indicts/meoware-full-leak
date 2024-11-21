from flask import Flask, render_template_string, request, jsonify, flash, redirect, url_for, abort
global color_range
global clicksim_lock
global nearest_bone
global fov_vertical
global accelstate
global fov_horizontal
global dpi_vertical
global capture_key_bind
global capture_mode
global buttons_mask
global clicker_mode
global debugger_state
global manufacturer_global
global dev
global serial_number_global
global clicker_enabled
global click_delay
global current_color
global dpi_horizontal
global click_box
global key_listener
global capture_enabled
global pid_global
global clicker_key_bind
global mouse_listener
global accel_amount
global time_between_clicks
global clicksim_running
global vid_global
global aim_offset
import threading
import sys
from PyQt5.QtWidgets import QApplication, QMainWindow, QVBoxLayout, QWidget
from PyQt5.QtWebEngineWidgets import QWebEngineView
from PyQt5.QtCore import QUrl, Qt, QPoint
import requests
import hashlib
import inspect
import zipfile
import os
import shutil
import ctypes
import subprocess
from mss import mss
import numpy as np
import cv2
from pynput import keyboard, mouse
import json
from PyQt5.QtGui import QPainter, QPainterPath, QColor, QRegion
import hid
from PyQt5.QtCore import QRectF
import serial.tools.list_ports
import signal
import urllib.request
import tempfile
import time
from keyauth import *
import ctypes
import os
import win32security
from flask import Flask, jsonify
import ctypes
from PyQt5.QtCore import Qt, QPoint
from PyQt5.QtWidgets import QWidget, QVBoxLayout, QLabel
import sys
import threading
import ctypes
import os
from flask import Flask
from PyQt5.QtCore import Qt, QUrl, QPoint
from PyQt5.QtGui import QPainter, QColor, QPainterPath
from PyQt5.QtWidgets import QApplication, QMainWindow, QVBoxLayout, QWidget, QLabel, QPushButton
from PyQt5.QtWebEngineWidgets import QWebEngineView
from PyQt5.QtCore import Qt, QUrl, QPoint, pyqtSignal, QObject
from PyQt5.QtGui import QPainter, QColor, QPainterPath
from PyQt5.QtWidgets import QApplication, QMainWindow, QVBoxLayout, QWidget, QLabel, QPushButton
from PyQt5.QtWebEngineWidgets import QWebEngineView
from PyQt5.QtCore import Qt, QUrl, QPoint, pyqtSignal, QObject
from PyQt5.QtGui import QPainter, QColor, QPainterPath
from PyQt5.QtWidgets import QApplication, QMainWindow, QVBoxLayout, QWidget, QLabel, QPushButton
from PyQt5.QtWebEngineWidgets import QWebEngineView
from PyQt5.QtCore import Qt, QUrl, QPoint, pyqtSignal, QObject, QTimer
from PyQt5.QtGui import QPainter, QColor, QPainterPath
from PyQt5.QtWidgets import QApplication, QMainWindow, QVBoxLayout, QWidget, QLabel
from PyQt5.QtWebEngineWidgets import QWebEngineView
import math
import pyautogui
url = 'https://www.synware.cc/ksecure'
pid_global = None
vid_global = None
manufacturer_global = None
serial_number_global = None
MOUSE_LEFT = 1
MOUSE_RIGHT = 2
MOUSE_MIDDLE = 4
MOUSE_ALL = MOUSE_LEFT | MOUSE_RIGHT | MOUSE_MIDDLE
buttons_mask = 0
dev = None

class DeviceNotFoundError(Exception):
    pass

def limit_xy(xy):
    if xy < -32767:
        return -32767
    if xy > 32767:
        return 32767
    return xy

def low_byte(x):
    return x & 255

def high_byte(x):
    return x >> 8 & 255

def _make_report(x, y):
    report_data = [1, buttons_mask, low_byte(x), high_byte(x), low_byte(y), high_byte(y)]
    return report_data

def _send_raw_report(report_data):
    dev.write(report_data)

def update_buttons(new_buttons):
    global buttons_mask
    if new_buttons != buttons_mask:
        buttons_mask = new_buttons
        move_mouse(0, 0)

def click_mouse(button=MOUSE_LEFT):
    global buttons_mask
    buttons_mask = button
    move_mouse(0, 0)
    buttons_mask = 0
    move_mouse(0, 0)

def press_button(button=MOUSE_LEFT):
    update_buttons(buttons_mask | button)

def release_button(button=MOUSE_LEFT):
    update_buttons(buttons_mask & ~button)
    time.sleep(time_between_clicks / 10)

def is_button_pressed(button=MOUSE_LEFT):
    return bool(button & buttons_mask)

def move_mouse(x, y):
    limited_x = limit_xy(x)
    limited_y = limit_xy(y)
    _send_raw_report(_make_report(limited_x, limited_y))

def get_position():
    report = _make_report(0, 0)
    return (report[2] + (report[3] << 8), report[4] + (report[5] << 8))

def check_ping(dev, ping_code):
    dev.write([0, ping_code])
    resp = dev.read(max_length=1, timeout_ms=10)
    return resp and resp[0] == ping_code

def find_mouse_device(vid, pid, ping_code, manufacturer_string, serial_number):
    global dev
    for dev_info in hid.enumerate(vid, pid):
        if dev_info['manufacturer_string'] == manufacturer_string and dev_info['serial_number'] == serial_number:
            try:
                dev = hid.device()
                dev.open_path(dev_info['path'])
                found = check_ping(dev, ping_code)
                if found:
                    return dev
                dev.close()
            except Exception as e:
                print(f'Error initializing device: {e}')
    else:
        return None

def get_mouse(vid, pid, manufacturer_string, serial_number, ping_code=249):
    global dev
    dev = find_mouse_device(vid, pid, ping_code, manufacturer_string, serial_number)
    if not dev:
        raise DeviceNotFoundError(f'[-] Device Vendor ID: {hex(vid)}, Product ID: {hex(pid)} not found!')
    move_mouse(0, 0)

def list_connected_mice():
    try:
        devices = hid.enumerate()
        mice = [dev for dev in devices if dev['usage_page'] == 1 and dev['usage'] == 2]
        for mouse in mice:
            print('Device:', mouse['product_string'])
            print('  Manufacturer:', mouse['manufacturer_string'])
            print('  Product:', mouse['product_string'])
            print('  Serial Number:', mouse['serial_number'])
            print('  Vendor ID:', hex(mouse['vendor_id']))
            print('  Product ID:', hex(mouse['product_id']))
            print('  Path:', mouse['path'])
            print('  Usage Page:', hex(mouse['usage_page']))
            print('  Usage:', hex(mouse['usage']))
            print()
    except Exception as e:
        print('An error occurred:', e)
MOUSE_LEFT = 1
MOUSE_RIGHT = 2
MOUSE_MIDDLE = 4
MOUSE_ALL = MOUSE_LEFT | MOUSE_RIGHT | MOUSE_MIDDLE
buttons_mask = 0
app = Flask('Keras')
app.secret_key = '34187879123478927827889274235032509832589023589089538239058097823509873259085329087'
login_state = {'logged_in': False}

def show_error_message(message):
    MB_OK = 0
    MB_ICONERROR = 16
    ctypes.windll.user32.MessageBoxW(None, message, 'Error', MB_OK | MB_ICONERROR)
try:

    def make_request(url):
        try:
            response = requests.get(url)
            response.raise_for_status()
            print('Request was successful!')
            print('Continuing with further operations...')
        except requests.exceptions.HTTPError as http_err:
            print(f'HTTP error occurred: {http_err}')
            sys.exit(1)
        except Exception as err:
            print(f'Other error occurred: {err}')
            sys.exit(1)
    make_request(url)
    app = Flask(__name__)
    app.secret_key = '34187879123478927827889274235032509832589023589089538239058097823509873259085329087'
    INSTALL_PATH = os.getenv('APPDATA')
    ZIP_FILE_PATH_EXE = os.path.join(INSTALL_PATH, 'files.zip')
    color_ranges = {'Red': [[0, 171, 241], [3, 255, 255]], 'Purple': [[142, 113, 162], [150, 157, 255]], 'Yellow': [[30, 136, 191], [30, 255, 255]]}
    current_color = 'Red'
    color_range = color_ranges[current_color]
    capture_enabled = False
    clicker_enabled = False
    capture_mode = 'toggle'
    clicker_mode = 'toggle'
    capture_key_bind = 'F11'
    clicker_key_bind = 'F12'
    key_listener = None
    mouse_listener = None
    dpi_horizontal = 5
    dpi_vertical = 5
    fov_horizontal = 60
    fov_vertical = 60
    click_delay = 1
    time_between_clicks = 20
    click_box = 5
    login_state = {'logged_in': False}
    authconf = 'v4_authconfirmkey=synwarev4conf'
    clicksim_lock = threading.Lock()
    clicksim_running = False
    aim_offset = 'Head'
    accelstate = 'off'
    accel_amount = 1
    nearest_bone = 'off'
    wasdblock = 'off'
    debugger_state = 'off'

    def clicksim():
        global clicksim_running
        with clicksim_lock:
            clicksim_running = True
            button = MOUSE_LEFT
            update_buttons(buttons_mask | button)
            time.sleep(click_delay / 100)
            update_buttons(buttons_mask & ~button)
            time.sleep(time_between_clicks / 100)
            update_buttons(buttons_mask & ~button)
            clicksim_running = False

    def distance_between_points(x1, y1, x2, y2):
        return math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)

    def capture_screen():
        global precalculated_steps
        global dpi_horizontal
        global dpi_vertical
        with mss() as sct:
            focused_box = None
            box_center_x, box_center_y = (None, None)
            while True:
                if capture_enabled or clicker_enabled or debugger_state == 'on':
                    screen_width = sct.monitors[1]['width']
                    screen_height = sct.monitors[1]['height']
                    half_width = max(1, fov_horizontal / 2)
                    half_height = max(1, fov_vertical / 2)
                    capture_area = {'top': int(screen_height / 2 - half_height), 'left': int(screen_width / 2 - half_width), 'width': int(2 * half_width), 'height': int(2 * half_height)}
                    capture_area['top'] = max(0, capture_area['top'])
                    capture_area['left'] = max(0, capture_area['left'])
                    screenshot = sct.grab(capture_area)
                    img = np.array(screenshot)
                    hsv = cv2.cvtColor(img, cv2.COLOR_BGR2HSV)
                    mask = cv2.inRange(hsv, tuple(color_range[0]), tuple(color_range[1]))
                    contours, _ = cv2.findContours(mask, cv2.RETR_EXTERNAL, cv2.CHAIN_APPROX_SIMPLE)
                    boxes = []
                    for contour in contours:
                        x, y, w, h = cv2.boundingRect(contour)
                        boxes.append((x, y, x + w, y + h))
                    merged_boxes = merge_boxes(boxes, 9)
                    capture_center_x = int(capture_area['width'] / 2)
                    capture_center_y = int(capture_area['height'] / 2)
                    if debugger_state == 'on':
                        debug_img = img.copy()

                    def smooth_movement(current, target, factor=0.3):
                        """Smooth the mouse movement to reduce jitter."""
                        return current + (target - current) * factor

                    def calculate_distance(x1, y1, x2, y2):
                        """Calculate the distance between two points."""
                        return math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
                    if focused_box and focused_box in merged_boxes:
                        box = focused_box
                    else:

                        def calculate_box_distance(box):
                            nonlocal box_center_y
                            nonlocal shoulder_height
                            nonlocal box_center_x
                            shoulder_height = box[3] * 0.15
                            box_center_x = (box[0] + box[2]) / 2
                            box_center_y = (box[1] + box[3]) / 2
                            distance_x = box_center_x - capture_center_x
                            distance_y = box_center_y - capture_center_y
                            return distance_x ** 2 + distance_y ** 2
                        if merged_boxes:
                            closest_box = min(merged_boxes, key=calculate_box_distance)
                            focused_box = closest_box
                            box = closest_box
                            precalculated_steps = []
                        else:
                            focused_box = None
                            box = None
                    if capture_enabled and box:
                        if box_center_x is None or box_center_y is None:
                            continue
                        if nearest_bone == 'off':
                            if aim_offset == 'Head':
                                box_center_x = (box[0] + box[2]) / 2
                                shoulder_height = box[3] * 0.15
                                box_center_y = box[1] + shoulder_height * 0.5
                            elif aim_offset == 'Body':
                                box_center_x = (box[0] + box[2]) / 2
                                box_center_y = (box[1] + box[3]) / 2
                        elif nearest_bone == 'on':
                            box_center_x_body = (box[0] + box[2]) / 2
                            box_center_y_body = (box[1] + box[3]) / 2
                            box_center_x_head = (box[0] + box[2]) / 2
                            shoulder_height = box[3] * 0.15
                            box_center_y_head = box[1] + shoulder_height * 0.5
                            y_distance_to_body = abs(capture_center_y - box_center_y_body)
                            y_distance_to_head = abs(capture_center_y - box_center_y_head)
                            if y_distance_to_body < y_distance_to_head:
                                box_center_x = box_center_x_body
                                box_center_y = box_center_y_body
                            else:
                                box_center_x = box_center_x_head
                                box_center_y = box_center_y_head
                        if dpi_horizontal < 4:
                            dpi_horizontal = 4
                        if dpi_vertical < 4:
                            dpi_vertical = 4
                        step_size_x = dpi_horizontal
                        step_size_y = dpi_vertical
                        state_percentage_map = {'on5': 0.05, 'on10': 0.1, 'on15': 0.15, 'on20': 0.2, 'on25': 0.25, 'on30': 0.3, 'on35': 0.35}
                        if debugger_state == 'on':
                            cv2.line(debug_img, (capture_center_x, capture_center_y), (int(box_center_x), int(box_center_y)), (0, 255, 0), 2)
                            cv2.circle(debug_img, (int(box_center_x), int(box_center_y)), click_box, (0, 0, 255), 2)
                        if accelstate in state_percentage_map:
                            delta_x = box_center_x - capture_center_x
                            delta_y = box_center_y - capture_center_y
                            percentage = state_percentage_map[accelstate]
                            slowdown_x_threshold = abs(fov_horizontal * percentage)
                            slowdown_y_threshold = abs(fov_vertical * percentage)
                            if debugger_state == 'on':
                                if abs(delta_x) <= slowdown_x_threshold or abs(delta_y) <= slowdown_y_threshold:
                                    cv2.line(debug_img, (capture_center_x, capture_center_y), (int(box_center_x), int(box_center_y)), (0, 0, 255), 2)
                            if abs(delta_x) <= slowdown_x_threshold:
                                move_x = min(step_size_x, max(-step_size_x, delta_x)) / accel_amount
                            else:
                                move_x = min(step_size_x, max(-step_size_x, delta_x))
                            if abs(delta_y) <= slowdown_y_threshold:
                                move_y = min(step_size_y, max(-step_size_y, delta_y)) / accel_amount
                            else:
                                move_y = min(step_size_y, max(-step_size_y, delta_y))
                        else:
                            delta_x = box_center_x - capture_center_x
                            delta_y = box_center_y - capture_center_y
                            move_x = min(step_size_x, max(-step_size_x, delta_x))
                            move_y = min(step_size_y, max(-step_size_y, delta_y))
                        move_x = smooth_movement(0, move_x)
                        move_y = smooth_movement(0, move_y)
                        move_mouse(int(move_x), int(move_y))
                    elif debugger_state == 'on' and box:
                        box_center_x = (box[0] + box[2]) / 2
                        shoulder_height = box[3] * 0.15
                        box_center_y = box[1] + shoulder_height * 0.5
                        cv2.line(debug_img, (capture_center_x, capture_center_y), (int(box_center_x), int(box_center_y)), (0, 0, 255), 2)
                        cv2.circle(debug_img, (int(box_center_x), int(box_center_y)), click_box, (0, 0, 255), 2)
                    if clicker_enabled and box_center_x is not None and (box_center_y is not None):
                        capture_center_x = capture_area['width'] / 2
                        capture_center_y = capture_area['height'] / 2
                        distance_x = box_center_x - capture_center_x
                        distance_y = box_center_y - capture_center_y
                        if debugger_state == 'on':
                            cv2.circle(debug_img, (int(box_center_x), int(box_center_y)), click_box, (0, 255, 0), 2)
                        if abs(distance_x) <= click_box and abs(distance_y) <= click_box and (not clicksim_running):
                            threading.Thread(target=clicksim).start()
                    if debugger_state == 'on':
                        cv2.imshow('Debugging Window', debug_img)
                    if cv2.waitKey(1) & 255 == ord('q'):
                        break
                else:
                    cv2.destroyAllWindows()

    def merge_boxes(boxes, distance):

        def overlap(box1, box2, distance):
            return box1[0] <= box2[2] + distance and box1[2] >= box2[0] - distance and (box1[1] <= box2[3] + distance) and (box1[3] >= box2[1] - distance)
        parent = list(range(len(boxes)))
        rank = [0] * len(boxes)

        def find(x):
            if parent[x] != x:
                parent[x] = find(parent[x])
            return parent[x]

        def union(x, y):
            rootX = find(x)
            rootY = find(y)
            if rootX != rootY:
                if rank[rootX] > rank[rootY]:
                    parent[rootY] = rootX
                elif rank[rootX] < rank[rootY]:
                    parent[rootX] = rootY
                else:
                    parent[rootY] = rootX
                    rank[rootX] += 1
        for i in range(len(boxes)):
            for j in range(i + 1, len(boxes)):
                if overlap(boxes[i], boxes[j], distance):
                    union(i, j)
        groups = {}
        for i in range(len(boxes)):
            root = find(i)
            if root not in groups:
                groups[root] = []
            groups[root].append(boxes[i])
        merged_boxes = []
        for group in groups.values():
            x1 = min((box[0] for box in group))
            y1 = min((box[1] for box in group))
            x2 = max((box[2] for box in group))
            y2 = max((box[3] for box in group))
            merged_boxes.append((x1, y1, x2, y2))
        return merged_boxes

    def on_press(key):
        global clicker_enabled
        global capture_enabled
        try:
            if hasattr(key, 'char') and key.char == capture_key_bind:
                if capture_mode == 'toggle':
                    capture_enabled = not capture_enabled
                elif capture_mode == 'hold':
                    capture_enabled = True
            elif hasattr(key, 'name') and key.name == capture_key_bind:
                if capture_mode == 'toggle':
                    capture_enabled = not capture_enabled
                elif capture_mode == 'hold':
                    capture_enabled = True
            if hasattr(key, 'char') and key.char == clicker_key_bind:
                if clicker_mode == 'toggle':
                    clicker_enabled = not clicker_enabled
                elif clicker_mode == 'hold':
                    clicker_enabled = True
            elif hasattr(key, 'name'):
                if key.name == clicker_key_bind:
                    if clicker_mode == 'toggle':
                        clicker_enabled = not clicker_enabled
                    elif clicker_mode == 'hold':
                        clicker_enabled = True
        except Exception as e:
            print(e)

    def on_release(key):
        global clicker_enabled
        global capture_enabled
        try:
            if hasattr(key, 'char') and key.char == capture_key_bind and (capture_mode == 'hold'):
                capture_enabled = False
            elif hasattr(key, 'name') and key.name == capture_key_bind and (capture_mode == 'hold'):
                capture_enabled = False
            if hasattr(key, 'char') and key.char == clicker_key_bind and (clicker_mode == 'hold'):
                clicker_enabled = False
            elif hasattr(key, 'name') and key.name == clicker_key_bind and (clicker_mode == 'hold'):
                clicker_enabled = False
        except Exception as e:
            print(e)

    def on_mouse_click(x, y, button, pressed):
        global clicker_enabled
        global capture_enabled
        try:
            if button == capture_key_bind:
                if capture_mode == 'toggle' and pressed:
                    capture_enabled = not capture_enabled
                elif capture_mode == 'hold':
                    capture_enabled = pressed
            if button == clicker_key_bind:
                if clicker_mode == 'toggle' and pressed:
                    clicker_enabled = not clicker_enabled
                elif clicker_mode == 'hold':
                    clicker_enabled = pressed
        except Exception as e:
            print(e)

    def start_listening():
        global mouse_listener
        global key_listener
        if key_listener:
            key_listener.stop()
        if mouse_listener:
            mouse_listener.stop()
        key_listener = keyboard.Listener(on_press=on_press, on_release=on_release)
        mouse_listener = mouse.Listener(on_click=on_mouse_click)
        key_listener.start()
        mouse_listener.start()

    def record_capture_key_bind(key):
        global capture_key_bind
        try:
            if hasattr(key, 'char') and key.char is not None:
                capture_key_bind = key.char
            elif hasattr(key, 'name'):
                capture_key_bind = key.name
            print(f'New capture key bind: {capture_key_bind}')
            key_listener.stop()
            mouse_listener.stop()
            start_listening()
        except Exception as e:
            print(e)

    def record_clicker_key_bind(key):
        global clicker_key_bind
        try:
            if hasattr(key, 'char') and key.char is not None:
                clicker_key_bind = key.char
            elif hasattr(key, 'name'):
                clicker_key_bind = key.name
            print(f'New clicker key bind: {clicker_key_bind}')
            key_listener.stop()
            mouse_listener.stop()
            start_listening()
        except Exception as e:
            print(e)

    def record_mouse_bind(x, y, button, pressed):
        global capture_key_bind
        global clicker_key_bind
        try:
            if pressed:
                if capture_key_bind is None:
                    capture_key_bind = button
                    print(f'New capture mouse bind: {capture_key_bind}')
                elif clicker_key_bind is None:
                    clicker_key_bind = button
                    print(f'New clicker mouse bind: {clicker_key_bind}')
                key_listener.stop()
                mouse_listener.stop()
                start_listening()
        except Exception as e:
            print(e)

    def login_required(f):

        def wrap(*args, **kwargs):
            if not login_state['logged_in']:
                return redirect(url_for('login'))
            return f(*args, **kwargs)
        wrap.__name__ = f.__name__
        return wrap

    def is_admin():
        try:
            return ctypes.windll.shell32.IsUserAnAdmin()
        except:
            return False

    def get_user_sid():
        try:
            username = os.getlogin()
            domain = os.getenv('USERDOMAIN')
            sid, domain, type = win32security.LookupAccountName(domain, username)
            return win32security.ConvertSidToStringSid(sid)
        except Exception as e:
            return f'An error occurred while retrieving the user SID: {e}'
    client = Keyauth(name='Synware', owner_id='KjaimltB2R', secret='e086d7d40ad4b3c80675c8475da7cfd5f564f59033927c14f8709183739f037a', version='1.0', file_hash=get_user_sid())

    @app.route('/')
    @app.route('/login')
    def login():
        return render_template_string(login_template)

    @app.route('/login', methods=['POST'])
    def login_post():
        username = request.form['username']
        password = f'{authconf}' + request.form['password']
        try:
            client.login(username=username, password=password)
            login_state['logged_in'] = True
            flash('Login successful!', 'success')
            start_listening()
            return redirect(url_for('connection'))
        except Exception as e:
            flash('Invalid credentials', 'danger')
            return redirect(url_for('login'))

    @app.route('/register')
    def register():
        return render_template_string(register_template)

    @app.route('/register', methods=['POST'])
    def register_post():
        username = request.form['username']
        password = f'{authconf}' + request.form['password']
        key = request.form['key']
        if key.startswith('Keras-'):
            client.register(username=username, password=password, license_key=key)
            flash('Auth success', 'success')
            return redirect(url_for('login'))
        flash('Invalid key', 'danger')
        return redirect(url_for('register'))

    @app.route('/aim')
    @login_required
    def aim():
        return render_template_string(html_template, title='Mouse', content='Aimbot settings', dpi_horizontal=dpi_horizontal, dpi_vertical=dpi_vertical, fov_horizontal=fov_horizontal, fov_vertical=fov_vertical, accel_amount=accel_amount, aim_offset=aim_offset, accelstate=accelstate, nearest_bone=nearest_bone)

    @app.route('/autoclick')
    @login_required
    def autoclick():
        return render_template_string(html_template, title='Clicker', content='Triggerbot settings', delay=click_delay, time_between_clicks=time_between_clicks, click_box=click_box, clicker_mode=clicker_mode, clicker_key_bind=clicker_key_bind)

    @app.route('/settings')
    @login_required
    def settings():
        return render_template_string(html_template, title='Settings', content='Legacy settings', capture_mode=capture_mode, current_color=current_color, capture_key_bind=capture_key_bind, debugger_state=debugger_state)

    @app.route('/save_config', methods=['POST'])
    @login_required
    def save_config():
        config_name = request.form.get('config_name')
        if config_name:
            desktop_path = os.path.join(os.path.join(os.path.expanduser('~')), 'Desktop')
            config_file_path = os.path.join(desktop_path, f'{config_name}.json')
            config_data = {'horizontal_lockspeed': dpi_horizontal, 'vertical_lockspeed': dpi_vertical, 'fov_horizontal': fov_horizontal, 'fov_vertical': fov_vertical, 'enemy_outline': current_color, 'aimbot_keybind_mode': capture_mode, 'aimbot_keybind': str(capture_key_bind), 'trigger_delay': click_delay, 'time_between_clicks': time_between_clicks, 'hitbox_zone': click_box, 'triggerbot_keybind_mode': clicker_mode, 'triggerbot_keybind': str(clicker_key_bind), 'accelstate': str(accelstate), 'accel_amount': str(accel_amount), 'nearest_bone': str(nearest_bone), 'debugger_state': str(debugger_state)}
            with open(config_file_path, 'w') as config_file:
                json.dump(config_data, config_file)
            return redirect(url_for('settings'))
        return redirect(url_for('settings'))

    @app.route('/import_config', methods=['POST'])
    @login_required
    def import_config():
        global dpi_horizontal
        global accelstate
        global current_color
        global click_box
        global debugger_state
        global clicker_mode
        global click_delay
        global fov_vertical
        global time_between_clicks
        global capture_mode
        global nearest_bone
        global accel_amount
        global capture_key_bind
        global clicker_key_bind
        global color_range
        global dpi_vertical
        global fov_horizontal
        if 'config_file' not in request.files:
            flash('No file part', 'danger')
            return redirect(url_for('settings'))
        file = request.files['config_file']
        if file.filename == '':
            flash('No selected file', 'danger')
            return redirect(url_for('settings'))
        if file:
            try:
                config_content = file.read().decode('utf-8')
                config_data = json.loads(config_content)
                dpi_horizontal = config_data.get('horizontal_lockspeed', dpi_horizontal)
                dpi_vertical = config_data.get('vertical_lockspeed', dpi_vertical)
                fov_horizontal = config_data.get('fov_horizontal', fov_horizontal)
                fov_vertical = config_data.get('fov_vertical', fov_vertical)
                current_color = config_data.get('enemy_outline', current_color)
                color_range = color_ranges[current_color]
                capture_mode = config_data.get('aimbot_keybind_mode', capture_mode)
                capture_key_bind = config_data.get('aimbot_keybind', capture_key_bind)
                click_delay = config_data.get('trigger_delay', click_delay)
                time_between_clicks = config_data.get('time_between_clicks', time_between_clicks)
                click_box = config_data.get('hitbox_zone', click_box)
                clicker_mode = config_data.get('triggerbot_keybind_mode', clicker_mode)
                clicker_key_bind = config_data.get('triggerbot_keybind', clicker_key_bind)
                debugger_state = config_data.get('debugger_state', debugger_state)
                accel_amount = config_data.get('accel_amount', accel_amount)
                nearest_bone = config_data.get('nearest_bone', nearest_bone)
                accelstate = config_data.get('accelstate', accelstate)
                start_listening()
                flash('Config file imported and settings applied.', 'success')
                return redirect(url_for('settings'))
            except:
                flash('Failed to import config file.', 'danger')
                return redirect(url_for('settings'))
        flash('Failed to import config file.', 'danger')
        return redirect(url_for('settings'))

    @app.route('/upgrade')
    @login_required
    def upgrade():
        return 'Upgrade page (under construction)'

    @app.route('/set_color_range', methods=['POST'])
    @login_required
    def set_color_range():
        global color_range
        global current_color
        color = request.form['color']
        if color in color_ranges:
            current_color = color
            color_range = color_ranges[current_color]
        return ('', 204)

    @app.route('/set_debug_state', methods=['POST'])
    @login_required
    def set_debug_state():
        global debugger_state
        state_debug = request.form['debug']
        debugger_state = state_debug
        return ('', 204)

    @app.route('/set_capture_mode', methods=['POST'])
    @login_required
    def set_capture_mode():
        global capture_mode
        capture_mode = request.form['mode']
        return ('', 204)

    @app.route('/set_clicker_mode', methods=['POST'])
    @login_required
    def set_clicker_mode():
        global clicker_mode
        clicker_mode = request.form['mode']
        return ('', 204)

    @app.route('/set_capture_key_bind', methods=['POST'])
    @login_required
    def set_capture_key_bind_route():
        global capture_key_bind
        global mouse_listener
        global key_listener
        if key_listener:
            key_listener.stop()
        if mouse_listener:
            mouse_listener.stop()
        capture_key_bind = None
        key_listener = keyboard.Listener(on_press=record_capture_key_bind)
        mouse_listener = mouse.Listener(on_click=record_mouse_bind)
        key_listener.start()
        mouse_listener.start()
        while capture_key_bind is None:
            time.sleep(0.0001)
        key_listener.stop()
        mouse_listener.stop()
        return redirect(url_for('keybinds'))

    @app.route('/set_clicker_key_bind', methods=['POST'])
    @login_required
    def set_clicker_key_bind_route():
        global clicker_key_bind
        global mouse_listener
        global key_listener
        if key_listener:
            key_listener.stop()
        if mouse_listener:
            mouse_listener.stop()
        clicker_key_bind = None
        key_listener = keyboard.Listener(on_press=record_clicker_key_bind)
        mouse_listener = mouse.Listener(on_click=record_mouse_bind)
        key_listener.start()
        mouse_listener.start()
        while clicker_key_bind is None:
            time.sleep(0.0001)
        key_listener.stop()
        mouse_listener.stop()
        return redirect(url_for('keybinds'))

    @app.route('/set_dpi_fov', methods=['POST'])
    @login_required
    def set_dpi_fov():
        global dpi_horizontal
        global accelstate
        global aim_offset
        global fov_vertical
        global nearest_bone
        global accel_amount
        global dpi_vertical
        global fov_horizontal
        dpi_horizontal = float(request.form['dpi_horizontal'])
        dpi_vertical = float(request.form['dpi_vertical'])
        fov_horizontal = int(request.form['fov_horizontal'])
        fov_vertical = int(request.form['fov_vertical'])
        aim_offset = str(request.form['hitbox'])
        accel_amount = int(request.form['accel_amount'])
        accelstate = str(request.form['accelstate'])
        nearest_bone = str(request.form['nearest_bone'])
        return ('', 204)

    @app.route('/set_clicker_settings', methods=['POST'])
    @login_required
    def set_clicker_settings():
        global time_between_clicks
        global click_delay
        global click_box
        click_delay = int(request.form['delay'])
        time_between_clicks = int(request.form['time_between_clicks'])
        click_box = int(request.form['click_box'])
        return ('', 204)

    @app.route('/firmware')
    @login_required
    def firmware():
        mouse_devices = list_mouse_devices()
        com_ports = list_serial_ports()
        return render_template_string(html_template, title='Firmware', content='Select firmware options', com_ports=com_ports, mice=mouse_devices, firmwares=['Please request a manual flash.', 'Please request a manual flash.', 'Please request a manual flash.'])

    @app.route('/keybinds')
    @login_required
    def keybinds():
        keybinds_data = {'clicker_key_bind': clicker_key_bind, 'clicker_mode': clicker_mode, 'capture_key_bind': capture_key_bind, 'capture_mode': capture_mode}
        return render_template_string(html_template, title='Keybinds', **keybinds_data)

    @app.route('/refresh_firmware', methods=['POST'])
    @login_required
    def refresh_firmware():
        return redirect(url_for('firmware'))

    @app.route('/reset_firmware', methods=['POST'])
    @login_required
    def reset_firmware():
        flash('Selections have been reset.', 'success')
        return redirect(url_for('firmware'))

    @app.route('/exit_application', methods=['POST'])
    @login_required
    def exit_application():
        os.kill(os.getpid(), signal.SIGINT)
        return redirect(url_for('index'))

    @app.route('/connection')
    @login_required
    def connection():
        mouse_devices = list_mouse_devices()
        return render_template_string(html_template, title='Connection', content='Connection settings', mice=mouse_devices)

    @app.route('/test_connection', methods=['POST'])
    @login_required
    def test_connection():
        global manufacturer_global
        global vid_global
        global pid_global
        global serial_number_global
        try:
            mouse = request.form.get('mouse')
            vid, pid = mouse.split('-')
            vid_global = int(vid, 16)
            pid_global = int(pid, 16)
            print(f'VID: {vid_global}, PID: {pid_global}')
            device = hid.device()
            device.open(vid_global, pid_global)
            manufacturer_global = device.get_manufacturer_string()
            serial_number_global = device.get_serial_number_string()
            print(f'Manufacturer: {manufacturer_global}')
            print(f'Serial Number: {serial_number_global}')
            get_mouse(vid_global, pid_global, manufacturer_global, serial_number_global)
            move_mouse(100, 100)
            flash(f'Connection successful with VID: {vid_global}, PID: {pid_global}', 'success')
            return redirect(url_for('connection', vid=vid_global, pid=pid_global, connection_status='Success'))
        except Exception as e:
            print(f'Error: {e}')
            flash(f'Connection failed: {str(e)}', 'danger')
            return redirect(url_for('connection', vid=vid_global, pid=pid_global, connection_status='Failed'))
        else:
            if False:
                device.close()

    def list_mouse_devices():
        devices = hid.enumerate()
        mouse_devices = set()
        for device in devices:
            if device['usage_page'] == 1 and device['usage'] == 2:
                vid = '{:04X}'.format(device['vendor_id'])
                pid = '{:04X}'.format(device['product_id'])
                name = device['manufacturer_string'] + ' ' + device['product_string']
                mouse_devices.add((vid, pid, name))
        return list(mouse_devices)

    def list_serial_ports():
        ports = ['COM%s' % (i + 1) for i in range(256)]
        available_ports = []
        for port in ports:
            try:
                s = serial.Serial(port)
                s.close()
                available_ports.append(port)
            except:
                pass
        return available_ports

    def extract_vid_pid(vid_selection_var):
        parts = vid_selection_var.split()
        vid_index = parts.index('VID:')
        pid_index = parts.index('PID:')
        vid = ''.join(filter(lambda x: x.isdigit() or x.lower() in 'abcdef', parts[vid_index + 1]))
        pid = ''.join(filter(lambda x: x.isdigit() or x.lower() in 'abcdef', parts[pid_index + 1]))
        return (vid, pid)
    html_template = '\n<!DOCTYPE html>\n<html lang="en">\n<head>\n    <meta charset="UTF-8">\n    <meta name="viewport" content="width=device-width, initial-scale=1.0">\n    <title>{{ title }}</title>\n    <link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.0.0-beta3/css/all.min.css">\n    <style>\n       @import url(\'https://fonts.googleapis.com/css2?family=Montserrat:wght@400&display=swap\');\n\n\n        body {\n            font-family: \'Roboto\', sans-serif; /* Simpler font */\n            margin: 0;\n            background: #000000;\n            color: #ffffff;\n            display: flex;\n            justify-content: center;\n            align-items: center;\n            height: 100vh;\n            transition: all 0.3s ease;\n            overflow: hidden;\n            user-select: none; /* Disable text selection */\n        }\n\n        .window {\n            background: #000000;\n            border-radius: 0px;\n            box-shadow: 0 0 0px rgba(0, 0, 0, 0.9);\n            display: flex;\n            flex-direction: column;\n            width: 670px; /* Adjusted width */\n            height: 420px; /* Adjusted height */\n            position: relative;\n            border: 0px solid #222;\n        }\n\n        .green-line {\n            width: 100%;\n            height: 4px;\n            background-color: #9c8dfd;\n            position: absolute;\n            top: 0;\n            left: 0;\n            z-index: 1001;\n            box-shadow: 0 0 10px #9c8dfd;\n        }\n\n        .content-wrapper {\n            display: flex;\n            flex-grow: 1;\n            position: relative;\n            padding-top: 5px; /* 10px padding below the green-line */\n        }\n\n        .sidebar {\n            width: 60px;\n            background-color: #000;\n            display: flex;\n            flex-direction: column;\n            justify-content: flex-start;\n            align-items: center;\n            padding: 0px 0;\n            box-shadow: 2px 0 10px rgba(0, 0, 0, 0.8);\n            border-right: 1px solid #151515;\n        }\n\n        .sidebar h2 img {\n            width: 20px;\n            height: auto;\n        }\n\n        .sidebar ul {\n            list-style: none;\n            padding: 0;\n            margin: 0;\n            display: flex;\n            flex-direction: column;\n            align-items: center;\n        }\n\n        .sidebar ul li {\n            margin-bottom: 25px;\n        }\n\n        .sidebar ul li a {\n            color: #888;\n            transition: color 0.3s ease;\n            font-size: 1.2rem;\n            display: block;\n            text-decoration: none;\n            outline: none; /* Remove orange focus box */\n        }\n\n        .sidebar ul li a:focus {\n            outline: none; /* Remove default focus behavior */\n        }\n\n        .sidebar ul li a:hover {\n            color: #fff;\n        }\n\n        .sidebar ul li.active a {\n            color: #9c8dfd;\n            font-weight: bold;\n        }\n\n        .sidebar ul li.exit {\n            margin-top: 10px; /* 10px spacing from top */\n        }\n\n        .content {\n            padding: 20px;\n            flex-grow: 1;\n            background: #020202;\n            box-shadow: inset 0 0 15px rgba(0, 0, 0, 0.5);\n            border-left: 1px solid #222;\n        }\n\n        .container {\n            width: 100%;\n            max-width: 600px;\n            margin: 0 auto;\n        }\n\n        /* Mouse Settings Grid Style */\n        {% if title == \'Mouse\' %} \n        .grid-container {\n            display: grid;\n            grid-template-columns: 1fr 1fr;\n            gap: 20px; /* Reduced gap between items to 10px */\n            margin-bottom: 20px; /* Added more spacing under the grid */\n        }\n\n        .grid-item {\n            display: flex;\n            flex-direction: column;\n            margin-bottom: 0px;\n        }\n\n        .grid-item label {\n            margin-bottom: 5px;\n            color: #a0a0a0;\n        }\n\n        .grid-item input,\n        .grid-item select {\n            padding: 8px;\n            background-color: #151515;\n            border: 1px solid #000000;\n            color: #fff;\n            border-radius: 6px;\n        }\n        {% endif %}\n\n        .form-group {\n            margin-bottom: 15px;\n            width: 100%;\n        }\n\n        .form-group label {\n            display: block;\n            margin-bottom: 5px;\n            color: #a0a0a0;\n        }\n\n        .form-group input,\n        .form-group select,\n        .form-group button {\n            width: 100%;\n            padding: 10px;\n            border-radius: 6px;\n            border: 1px solid #000000;\n            background-color: #151515;\n            color: #fff;\n            font-size: 0.9rem;\n            transition: all 0.3s ease;\n            box-sizing: border-box;\n        }\n\n        .form-group button {\n            background-color: #9c8dfd;\n            border: none;\n            cursor: pointer;\n            transition: background-color 0.3s ease;\n            box-shadow: 0 0 8px #9c8dfd;\n            color: #333;\n            font-weight: bold;\n            outline: none; /* Remove outline when button is clicked */\n        }\n\n        .form-group button:hover {\n            background-color: #b0a4ff;\n        }\n\n        h1 {\n            opacity: 0;\n            font-size: 0.1px;\n        }\n\n        input[type="range"] {\n            -webkit-appearance: none;\n            width: 100%;\n            height: 2px;\n            background: #0d0d0d;\n            border-radius: 5px;\n            outline: none;\n            transition: background 0.3s ease;\n            box-shadow: none;\n            position: relative;\n        }\n\n        input[type="range"]::-webkit-slider-thumb {\n            -webkit-appearance: none;\n            appearance: none;\n            width: 14px;\n            height: 14px;\n            background: #9c8dfd;\n            border-radius: 50%;\n            cursor: pointer;\n            position: relative;\n            top: -6px;\n            transition: background 0.3s ease, transform 0.2s ease;\n            box-shadow: 0 0 5px rgba(255, 255, 255, 0.5);\n            border: none;\n        }\n\n        input[type="range"]::-moz-range-thumb {\n            width: 14px;\n            height: 14px;\n            background: #9c8dfd;\n            border-radius: 50%;\n            cursor: pointer;\n            transition: background 0.3s ease, transform 0.2s ease;\n            border: none;\n        }\n\n        input[type="range"]:hover::-webkit-slider-thumb {\n            background: #9c8dfd;\n            transform: scale(1.1);\n        }\n\n        input[type="range"]:hover::-moz-range-thumb {\n            background: #9c8dfd;\n            transform: scale(1.1);\n        }\n\n        input[type="range"]::-webkit-slider-runnable-track {\n            width: 100%;\n            height: 2px;\n            background: #9c8dfd;\n            border-radius: 5px;\n            box-shadow: none;\n        }\n\n        input[type="range"]::-moz-range-track {\n            width: 100%;\n            height: 2px;\n            background: #9c8dfd;\n            border-radius: 5px;\n            box-shadow: none;\n        }\n\n        input[type="range"]:focus {\n            outline: none;\n        }\n\n        .pixel {\n            position: absolute;\n            width: 2px;\n            height: 2px;\n            background-color: #9c8dfd;\n            border-radius: 50%;\n            opacity: 1;\n        }\n\n        @keyframes sparkle {\n            0% {\n                transform: translateY(0) translateX(0);\n                opacity: 1;\n            }\n            100% {\n                transform: translateY(20px) translateX(calc(var(--random-x) * 10px));\n                opacity: 0;\n            }\n        }\n\n        .falling {\n            animation: sparkle 1s ease-out forwards;\n        }\n\n        .overlay {\n            position: fixed;\n            top: 0;\n            left: 0;\n            width: 100%;\n            height: 100%;\n            background: rgba(0, 0, 0, 0.9);\n            display: flex;\n            justify-content: center;\n            align-items: center;\n            z-index: 1000;\n            opacity: 0;\n            visibility: hidden;\n            transition: opacity 0.3s ease, visibility 0.3s ease;\n        }\n\n        .overlay.show {\n            opacity: 1;\n            visibility: visible;\n        }\n\n        .modal-container {\n            text-align: center;\n            color: #fff;\n            width: 300px;\n            padding: 20px;\n            background: #1a1a1a;\n            border-radius: 10px;\n            box-shadow: 0 0 20px #9c8dfd;\n        }\n\n        .modal-container button {\n            background-color: #9c8dfd;\n            border: none;\n            padding: 10px 20px;\n            border-radius: 5px;\n            cursor: pointer;\n            margin: 5px;\n            color: #333;\n            box-shadow: 0 0 8px #9c8dfd;\n            font-weight: bold;\n        }\n\n        .modal-container button:hover {\n            background-color: #b0a4ff;\n            box-shadow: 0 0 12px #9c8dfd;\n        }\n\n        .modal-container.popup {\n            transform: scale(0.8);\n            opacity: 0;\n            animation: popup 0.4s forwards;\n        }\n\n        @keyframes popup {\n            to {\n                transform: scale(1);\n                opacity: 1;\n            }\n        }\n\n        .progress-container {\n            text-align: center;\n            color: #fff;\n            width: 150px;\n            margin: auto;\n            display: block; /* Changed to block to ensure no unwanted flexbox behavior */\n        }\n\n        .progress-bar {\n            width: 100%;\n            background-color: #444;\n            border-radius: 5px;\n            overflow: hidden;\n            margin-top: 10px;\n        }\n\n        .progress-bar-fill {\n            height: 20px;\n            width: 0;\n            background-color: #9c8dfd;\n            transition: width 1s ease;\n            box-shadow: 0 0 8px #9c8dfd;\n        }\n    </style>\n    <script>\n        document.addEventListener(\'contextmenu\', event => event.preventDefault());\n        document.addEventListener(\'dragstart\', event => event.preventDefault());\n\n        function showLoadingOverlay() {\n            const overlay = document.getElementById(\'overlay\');\n            const contentWrapper = document.querySelector(\'.content-wrapper\');\n            const progressContainer = document.querySelector(\'.progress-container\');\n\n            overlay.classList.add(\'show\');\n            contentWrapper.classList.add(\'blurred-content\');\n            progressContainer.style.display = \'block\';\n        }\n\n        function updateProgress(progress) {\n            const progressBarFill = document.getElementById(\'progress-bar-fill\');\n            progressBarFill.style.width = progress + \'%\';\n        }\n\n        function showFirmwareLoadingOverlay() {\n            const overlay = document.getElementById(\'overlay\');\n            const contentWrapper = document.querySelector(\'.content-wrapper\');\n            const progressContainer = document.querySelector(\'.progress-container\');\n\n            overlay.classList.add(\'show\');\n            contentWrapper.classList.add(\'blurred-content\');\n            progressContainer.style.display = \'block\';\n\n            let progress = 0;\n            const interval = setInterval(() => {\n                if (progress >= 100) {\n                    clearInterval(interval);\n                } else {\n                    progress += 10;\n                    updateProgress(progress);\n                }\n            }, 4500);\n        }\n\n        document.addEventListener(\'DOMContentLoaded\', function () {\n            const greenLine = document.querySelector(\'.green-line\');\n\n            function createSparkle() {\n                const pixel = document.createElement(\'div\');\n                pixel.classList.add(\'pixel\');\n                pixel.style.left = `${Math.random() * greenLine.offsetWidth}px`;\n                pixel.style.setProperty(\'--random-x\', Math.random() - 0.5);  // Random horizontal movement\n                greenLine.appendChild(pixel);\n\n                setTimeout(() => {\n                    pixel.classList.add(\'falling\');\n                }, 10);\n\n                setTimeout(() => {\n                    pixel.remove();\n                }, 1000); // Sparkles should disappear quickly\n            }\n\n            setInterval(createSparkle, 75); // 25% more sparkles\n        });\n    </script>\n</head>\n<body>\n    <div class="window">\n        <div class="green-line"></div>\n        <div class="content-wrapper">\n            <div class="sidebar">\n                <h2><img src="https://cdn.prod.website-files.com/6643cc453673bff4f58abdc4/66ffef07e442e9ceca25c62e_keras5.png" alt="Logo"></h2>\n                <ul>\n                    <li class="{% if title == \'Mouse\' %}active{% endif %}">\n                        <a href="/aim" draggable="false">\n                            <i class="fas fa-skull"></i>\n                        </a>\n                    </li>\n                    <li class="{% if title == \'Clicker\' %}active{% endif %}">\n                        <a href="/autoclick" draggable="false">\n                            <i class="fas fa-crosshairs"></i>\n                        </a>\n                    </li>\n                    <li class="{% if title == \'Keybinds\' %}active{% endif %}">\n                        <a href="/keybinds" draggable="false">\n                            <i class="fas fa-keyboard"></i>\n                        </a>\n                    </li>\n                </ul>\n                <ul>\n                    <li class="{% if title == \'Settings\' %}active{% endif %}">\n                        <a href="/settings" draggable="false">\n                            <i class="fas fa-cog"></i>\n                        </a>\n                    </li>\n                </ul>\n                <ul>\n                    <li class="{% if title == \'Firmware\' %}active{% endif %}">\n                        <a href="/firmware" draggable="false">\n                            <i class="fas fa-microchip"></i>\n                        </a>\n                    </li>\n                    <li class="{% if title == \'Connection\' %}active{% endif %}">\n                        <a href="/connection" draggable="false">\n                            <i class="fas fa-plug"></i>\n                        </a>\n                    </li>\n                </ul>\n                <ul>\n                    <li class="exit">\n                        <a href="javascript:void(0)" onclick="exitApplication()" class="exit-button" draggable="false">\n                            <i class="fas fa-sign-out-alt"></i>\n                        </a>\n                    </li>\n\n                    <!-- Hidden form -->\n                    <form id="exit-form" action="/exit_application" method="post" style="display: none;"></form>\n\n                    <script>\n                        function exitApplication() {\n                            // This will trigger the form submission\n                            document.getElementById(\'exit-form\').submit();\n                        }\n                    </script>\n                </ul>\n            </div>\n            <div class="content">\n                <div class="container">\n                    {% if title == \'Mouse\' %}\n                    <h1>Mouse Settings</h1>\n\n                    <div class="settings-container">\n                        <form method="post" action="/set_dpi_fov">\n                            <div class="grid-container">\n                                <div class="grid-item">\n                                    <label for="dpi_horizontal">Horizontal lockspeed</label>\n                                    <input type="text" id="dpi_horizontal" name="dpi_horizontal" placeholder="DPI horizontal" value="{{ dpi_horizontal }}" required>\n                                </div>\n                                <div class="grid-item">\n                                    <label for="dpi_vertical">Vertical lockspeed</label>\n                                    <input type="text" id="dpi_vertical" name="dpi_vertical" placeholder="DPI vertical" value="{{ dpi_vertical }}" required>\n                                </div>\n                                <div class="grid-item">\n                                    <label for="fov_horizontal">FOV Horizontal</label>\n                                    <input type="text" id="fov_horizontal" name="fov_horizontal" placeholder="FOV horizontal" value="{{ fov_horizontal }}" required>\n                                </div>\n                                <div class="grid-item">\n                                    <label for="fov_vertical">FOV Vertical</label>\n                                    <input type="text" id="fov_vertical" name="fov_vertical" placeholder="FOV vertical" value="{{ fov_vertical }}" required>\n                                </div>\n                                <div class="grid-item">\n                                    <label for="accel_amount">Acceleration strength</label>\n                                    <input type="number" id="accel_amount" name="accel_amount" placeholder="1" step="1" value="{{ accel_amount }}">\n                                </div>\n\n\n                                <div class="grid-item">\n                                    <label for="hitbox">Hitbox</label>\n                                    <select id="hitbox" name="hitbox" required>\n                                        <option value="Head" {% if aim_offset == \'Head\' %}selected{% endif %}>Head</option>\n                                        <option value="Neck" {% if aim_offset == \'Neck\' %}selected{% endif %}>Neck</option>\n                                        <option value="Body" {% if aim_offset == \'Body\' %}selected{% endif %}>Body</option>\n                                    </select>\n                                </div>\n\n\n                                <div class="grid-item">\n                                    <label for="accelstate">Acceleration</label>\n                                    <select id="accelstate" name="accelstate" required>\n                                        <option value="off" {% if accelstate == \'off\' %}selected{% endif %}>Acceleration off</option>\n                                        <option value="on5" {% if accelstate == \'on5\' %}selected{% endif %}>Acceleration 5%</option>\n                                        <option value="on10" {% if accelstate == \'on10\' %}selected{% endif %}>Acceleration 10%</option>\n                                        <option value="on15" {% if accelstate == \'on15\' %}selected{% endif %}>Acceleration 15%</option>\n                                        <option value="on20" {% if accelstate == \'on20\' %}selected{% endif %}>Acceleration 20%</option>\n                                        <option value="on25" {% if accelstate == \'on25\' %}selected{% endif %}>Acceleration 25%</option>\n                                        <option value="on30" {% if accelstate == \'on30\' %}selected{% endif %}>Acceleration 30%</option>\n                                        <option value="on35" {% if accelstate == \'on35\' %}selected{% endif %}>Acceleration 35%</option>\n                                    </select>\n                                </div>\n\n                                \n                                <div class="grid-item">\n                                    <label for="nearest_bone">Nearest bone</label>\n                                    <select id="nearest_bone" name="nearest_bone" required>\n                                        <option value="off" {% if nearest_bone == \'off\' %}selected{% endif %}>off</option>\n                                        <option value="on" {% if nearest_bone == \'on\' %}selected{% endif %}>on</option>\n                                    </select>\n                                </div>\n\n\n\n                            </div>\n                            <div class="form-group">\n                                <button type="submit" draggable="false">Confirm settings</button>\n                            </div>\n                        </form>\n                    </div>\n                    {% elif title == \'Clicker\' %}\n                    <h1>Clicker Settings</h1>\n                    <form method="post" action="/set_clicker_settings">\n                        <div class="form-group">\n                            <label for="delay">Spray time (ms): <span id="delay-value">{{ delay }}</span></label>\n                            <input type="range" id="delay" name="delay" min="1" max="50" value="{{ delay }}" oninput="document.getElementById(\'delay-value\').textContent = this.value" required>\n                        </div>\n                        <div class="form-group">\n                            <label for="time_between_clicks">Time Between Clicks (ms): <span id="time-between-clicks-value">{{ time_between_clicks }}</span></label>\n                            <input type="range" id="time_between_clicks" name="time_between_clicks" min="1" max="150" value="{{ time_between_clicks }}" oninput="document.getElementById(\'time-between-clicks-value\').textContent = this.value" required>\n                        </div>\n                        <div class="form-group">\n                            <label for="click_box">Hitbox zone: <span id="click-box-value">{{ click_box }}</span></label>\n                            <input type="range" id="click_box" name="click_box" min="1" max="30" value="{{ click_box }}" oninput="document.getElementById(\'click-box-value\').textContent = this.value" required>\n                        </div>\n                        <div class="form-group">\n                            <button type="submit" draggable="false">Confirm settings</button>\n                        </div>\n                    </form>\n                    {% elif title == \'Settings\' %}\n                    <h1>Settings</h1>\n                    <form method="post" action="/set_color_range" id="colorForm">\n                        <div class="form-group">\n                            <label for="color">Enemy outline color</label>\n                            <select id="color" class="select-box" name="color" onchange="document.getElementById(\'colorForm\').submit()" required>\n                                <option value="Red" {% if current_color == \'Red\' %}selected{% endif %}>Red</option>\n                                <option value="Purple" {% if current_color == \'Purple\' %}selected{% endif %}>Purple</option>\n                                <option value="Yellow" {% if current_color == \'Yellow\' %}selected{% endif %}>Yellow</option>\n                            </select>\n                        </div>\n                    </form>\n                    <form method="post" action="/set_debug_state" id="debugState">\n                        <div class="form-group">\n                            <label for="debug">Visuals debugger</label>\n                            <select id="debug" class="select-box" name="debug" onchange="document.getElementById(\'debugState\').submit()" required>\n                                <option value="on" {% if debugger_state == \'on\' %}selected{% endif %}>on</option>\n                                <option value="off" {% if debugger_state == \'off\' %}selected{% endif %}>off</option>\n                            </select>\n                        </div>\n                    </form>\n                    <form method="post" action="/save_config" id="save-config-form">\n                        <div class="form-group">\n                            <label for="config_name">Enter Config File Name</label>\n                            <input type="text" id="config_name" name="config_name" placeholder="Enter config file name" required>\n                        </div>\n                        <div class="form-group">\n                            <button type="submit" draggable="false">Save Config</button>\n                        </div>\n                    </form>\n                    <div class="form-group">\n                        <button onclick="document.getElementById(\'file-input\').click()" draggable="false">Import Config</button>\n                    </div>\n                    <form id="import-config-form" method="post" action="/import_config" enctype="multipart/form-data" style="display:none;">\n                        <input type="file" id="file-input" name="config_file" onchange="document.getElementById(\'import-config-form\').submit()" required>\n                    </form>\n                    {% if import_message %}\n                    <div class="message">{{ import_message }}</div>\n                    {% endif %}\n                    {% elif title == \'Keybinds\' %}\n                    <h1>Keybinds Settings</h1>\n                    <form method="post" action="/set_clicker_mode" id="clickerModeForm">\n                        <div class="form-group">\n                            <label for="clicker_mode">Triggerbot keybind settings</label>\n                            <select id="clicker_mode" class="select-box" name="mode" onchange="document.getElementById(\'clickerModeForm\').submit()" required>\n                                <option value="toggle" {% if clicker_mode == \'toggle\' %}selected{% endif %}>Toggle</option>\n                                <option value="hold" {% if clicker_mode == \'hold\' %}selected{% endif %}>Hold</option>\n                            </select>\n                        </div>\n                    </form>\n                    <form method="post" action="/set_clicker_key_bind">\n                        <div class="form-group">\n                            <button type="submit" draggable="false">Triggerbot keybind ({{ clicker_key_bind }})</button>\n                        </div>\n                    </form>\n                    <form method="post" action="/set_capture_mode" id="modeForm">\n                        <div class="form-group">\n                            <label for="mode">Aimbot keybind settings</label>\n                            <select id="mode" class="select-box" name="mode" onchange="document.getElementById(\'modeForm\').submit()" required>\n                                <option value="toggle" {% if capture_mode == \'toggle\' %}selected{% endif %}>Toggle</option>\n                                <option value="hold" {% if capture_mode == \'hold\' %}selected{% endif %}>Hold</option>\n                            </select>\n                        </div>\n                    </form>\n                    <form method="post" action="/set_capture_key_bind">\n                        <div class="form-group">\n                            <button type="submit" draggable="false">Aimbot keybind ({{ capture_key_bind }})</button>\n                        </div>\n                    </form>\n                    {% elif title == \'Firmware\' %}\n                    <h1>Firmware Settings</h1>\n                        <div class="form-group">\n                            <label for="manufacturer">Manufacturer</label>\n                            <input type="text" id="manufacturer" name="manufacturer" class="form-control" required>\n                        </div>\n                        <div class="form-group">\n                            <label for="usb_device_name">USB Device Name</label>\n                            <input type="text" id="usb_device_name" name="usb_device_name" class="form-control" required>\n                        </div>\n                        <div class="form-group">\n                            <label for="mouse">Select your mouse</label>\n                            <select id="mouse" name="mouse" class="form-control" required>\n                                {% for mouse in mice %}\n                                <option value="{{ mouse[0] }}-{{ mouse[1] }}">{{ mouse[2] }} (VID: {{ mouse[0] }}, PID: {{ mouse[1] }})</option>\n                                {% endfor %}\n                            </select>\n                        </div>\n                        <div class="form-group">\n                            <label for="firmware">Select firmware</label>\n                            <select id="firmware" name="firmware" class="form-control" required>\n                                {% for firmware in firmwares %}\n                                <option value="{{ firmware }}">{{ firmware }}</option>\n                                {% endfor %}\n                            </select>\n                        </div>\n                        <div class="form-group">\n                            <button type="submit" class="btn btn-primary" data-loading-text="Processing..." draggable="false">Spoof hardware</button>\n                        </div>\n                    </form>\n                    {% elif title == \'Connection\' %}\n                    <h1>Connection Settings</h1>\n                    <form method="post" action="/test_connection">\n                        <div class="form-group">\n                            <label for="mouse">Select your hardware</label>\n                            <select id="mouse" name="mouse" class="form-control" required>\n                                {% for mouse in mice %}\n                                <option value="{{ mouse[0] }}-{{ mouse[1] }}">{{ mouse[2] }} (VID: {{ mouse[0] }}, PID: {{ mouse[1] }})</option>\n                                {% endfor %}\n                            </select>\n                        </div>\n                        <div class="form-group">\n                            <button type="submit" draggable="false">Connect & Test Move</button>\n                        </div>\n                    </form>\n                    {% endif %}\n                </div>\n            </div>\n        </div>\n    </div>\n    <div class="overlay" id="overlay">\n        <div class="progress-container">\n            <p>Loading...</p>\n            <div class="progress-bar">\n                <div class="progress-bar-fill" id="progress-bar-fill"></div>\n            </div>\n        </div>\n    </div>\n    <form id="exit-form" action="/exit_application" method="post" style="display: none;"></form>\n</body>\n</html>\n    '
    login_template = '\n<!DOCTYPE html>\n<html lang="en">\n<head>\n    <meta charset="UTF-8">\n    <meta name="viewport" content="width=device-width, initial-scale=1.0">\n    <title>ИXZTWARE Login</title>\n    <style>\n        @import url(\'https://fonts.googleapis.com/css2?family=Roboto:wght@400&display=swap\'); /* Simpler font */\n        body {\n            font-family: \'Roboto\', sans-serif; /* Simpler font */\n            margin: 0;\n            background: #000000; /* Darker background */\n            color: #dcdcdc; /* Light text */\n            display: flex;\n            justify-content: center;\n            align-items: center;\n            height: 100vh;\n            transition: all 0.3s ease;\n            user-select: none;\n            -webkit-user-select: none;\n            overflow: hidden;\n            position: relative;\n        }\n        .green-line {\n            width: 100%;\n            height: 4px;\n            background-color: #9c8dfd; /* Red line */\n            position: absolute;\n            top: 0;\n            left: 0;\n            z-index: 1001;\n            box-shadow: 0 0 10px #9c8dfd;\n        }\n        .container {\n            background: #000000; /* Pure black container */\n            padding: 20px;\n            border-radius: 10px;\n            box-shadow: 0 0 30px rgba(0, 0, 0, 0.9); /* Stronger shadow */\n            text-align: center;\n            width: 300px;\n        }\n        h2 {\n            margin-bottom: 15px;\n            color: #9c8dfd; /* Red text */\n        }\n        .form-group {\n            margin-bottom: 15px;\n            text-align: left;\n            width: 100%;\n        }\n        .form-group label {\n            display: block;\n            margin-bottom: 5px;\n            color: #a0a0a0;\n        }\n        .form-group input, .form-group button {\n            width: 100%;\n            padding: 8px;\n            border-radius: 4px;\n            border: 1px solid #444;\n            background-color: #151515; /* Darker input fields */\n            color: #fff; /* Light text in inputs */\n            font-size: 0.9rem;\n            transition: all 0.3s ease;\n            box-sizing: border-box;\n        }\n        .form-group input:focus {\n            border-color: #9c8dfd; /* Red border on focus */\n            outline: none;\n        }\n        .form-group button {\n            border: none;\n            background-color: #9c8dfd; /* Red buttons */\n            color: #333; /* Darker text */\n            font-weight: bold;\n            font-size: 1rem;\n            cursor: pointer;\n            transition: background-color 0.3s ease;\n            margin-top: 10px;\n            box-shadow: 0 0 8px #9c8dfd; /* Red glow */\n        }\n        .form-group button:hover {\n            background-color: #b0a4ff;\n        }\n        .message {\n            margin-top: 10px;\n            padding: 8px;\n            background-color: #2a2a2e;\n            color: #fff;\n            border-radius: 4px;\n        }\n        .form-group a {\n            color: #9c8dfd; /* Red link */\n            text-decoration: none;\n        }\n        .form-group a:hover {\n            color: #b0a4ff;\n        }\n    </style>\n    <script>\n        document.addEventListener(\'contextmenu\', event => event.preventDefault());\n    </script>\n</head>\n<body>\n    <div class="green-line"></div> <!-- Green line at top of body -->\n    <div class="container">\n        <h2>Keras login</h2>\n        <form method="post" action="/login">\n            <div class="form-group">\n                <label for="username">Username</label>\n                <input type="text" id="username" name="username" placeholder="Enter username" required>\n            </div>\n            <div class="form-group">\n                <label for="password">Password</label>\n                <input type="password" id="password" name="password" placeholder="Enter password" required>\n            </div>\n            <div class="form-group">\n                <button type="submit">Login</button>\n            </div>\n        </form>\n        {% with messages = get_flashed_messages(with_categories=true) %}\n            {% if messages %}\n                {% for category, message in messages %}\n                    <div class="message {{ category }}">{{ message }}</div>\n                {% endfor %}\n            {% endif %}\n        {% endwith %}\n        <p>Don\'t have an account? <a href="/register">Register here</a></p>\n    </div>\n</body>\n</html>\n\n\n    '
    register_template = '\n<!DOCTYPE html>\n<html lang="en">\n<head>\n    <meta charset="UTF-8">\n    <meta name="viewport" content="width=device-width, initial-scale=1.0">\n    <title>Register</title>\n    <style>\n        @import url(\'https://fonts.googleapis.com/css2?family=Roboto:wght@400&display=swap\'); /* Simpler font */\n        body {\n            font-family: \'Roboto\', sans-serif; /* Simpler font */\n            margin: 0;\n            background: #000000; /* Darker background */\n            color: #dcdcdc; /* Light text */\n            display: flex;\n            justify-content: center;\n            align-items: center;\n            height: 100vh;\n            transition: all 0.3s ease;\n            user-select: none;\n            -webkit-user-select: none;\n            overflow: hidden;\n            position: relative;\n        }\n        .green-line {\n            width: 100%;\n            height: 4px;\n            background-color: #9c8dfd; /* Red line */\n            position: absolute;\n            top: 0;\n            left: 0;\n            z-index: 1001;\n            box-shadow: 0 0 10px #9c8dfd;\n        }\n        .container {\n            background: #000000; /* Pure black container */\n            padding: 20px;\n            border-radius: 10px;\n            box-shadow: 0 0 30px rgba(0, 0, 0, 0.9); /* Stronger shadow */\n            text-align: center;\n            width: 300px;\n        }\n        h2 {\n            margin-bottom: 15px;\n            color: #9c8dfd; /* Red text */\n        }\n        .form-group {\n            margin-bottom: 15px;\n            text-align: left;\n            width: 100%;\n        }\n        .form-group label {\n            display: block;\n            margin-bottom: 5px;\n            color: #a0a0a0;\n        }\n        .form-group input, .form-group button {\n            width: 100%;\n            padding: 8px;\n            border-radius: 4px;\n            border: 1px solid #444;\n            background-color: #151515; /* Darker input fields */\n            color: #fff; /* Light text in inputs */\n            font-size: 0.9rem;\n            transition: all 0.3s ease;\n            box-sizing: border-box;\n        }\n        .form-group input:focus {\n            border-color: #9c8dfd; /* Red border on focus */\n            outline: none;\n        }\n        .form-group button {\n            border: none;\n            background-color: #9c8dfd; /* Red buttons */\n            color: #333; /* Darker text */\n            font-weight: bold;\n            font-size: 1rem;\n            cursor: pointer;\n            transition: background-color 0.3s ease;\n            margin-top: 10px;\n            box-shadow: 0 0 8px #9c8dfd; /* Red glow */\n        }\n        .form-group button:hover {\n            background-color: #b0a4ff;\n        }\n        .message {\n            margin-top: 10px;\n            padding: 8px;\n            background-color: #2a2a2e;\n            color: #fff;\n            border-radius: 4px;\n        }\n        .form-group a {\n            color: #9c8dfd; /* Red link */\n            text-decoration: none;\n        }\n        .form-group a:hover {\n            color: #b0a4ff;\n        }\n    </style>\n    <script>\n        document.addEventListener(\'contextmenu\', event => event.preventDefault());\n    </script>\n</head>\n<body>\n    <div class="green-line"></div> <!-- Green line at top of body -->\n    <div class="container">\n        <h2>M9 REGISTER</h2>\n        <form method="post" action="/register">\n            <div class="form-group">\n                <label for="username">Username</label>\n                <input type="text" id="username" name="username" placeholder="Enter username" required>\n            </div>\n            <div class="form-group">\n                <label for="password">Password</label>\n                <input type="password" id="password" name="password" placeholder="Enter password" required>\n            </div>\n            <div class="form-group">\n                <label for="key">Key</label>\n                <input type="text" id="key" name="key" placeholder="Enter key" required>\n            </div>\n            <div class="form-group">\n                <button type="submit">Register</button>\n            </div>\n        </form>\n        {% with messages = get_flashed_messages(with_categories=true) %}\n            {% if messages %}\n                {% for category, message in messages %}\n                    <div class="message {{ category }}">{{ message }}</div>\n                {% endfor %}\n            {% endif %}\n        {% endwith %}\n        <p>Already have an account? <a href="/login">Login here</a></p>\n    </div>\n</body>\n</html>\n\n\n\n    '

    def run_flask_app():
        app.run(host='127.0.0.1', port=54535, debug=False)
    flask_thread = threading.Thread(target=run_flask_app)
    flask_thread.daemon = True
    flask_thread.start()
except Exception as e:
    show_error_message(f'Error occurred: {e}')

def hide_console():
    kernel32 = ctypes.windll.kernel32
    user32 = ctypes.windll.user32
    SW_HIDE = 0
    hWnd = kernel32.GetConsoleWindow()
    if hWnd:
        user32.ShowWindow(hWnd, SW_HIDE)

class StatusSignal(QObject):
    status_changed = pyqtSignal()
status_signal = StatusSignal()

class StatusOverlay(QWidget):

    def __init__(self, parent=None):
        super(StatusOverlay, self).__init__(parent)
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        layout = QVBoxLayout()
        self.capture_status_label = QLabel(self)
        self.clicker_status_label = QLabel(self)
        layout.addWidget(self.capture_status_label)
        layout.addWidget(self.clicker_status_label)
        self.setLayout(layout)
        self.adjustSize()
        self.move(parent.width() - self.width() - 0, 390)
        self.setStyleSheet('background: transparent;')
        self.update_status()
        status_signal.status_changed.connect(self.update_status)

    def update_status(self):
        capture_text = 'on' if capture_enabled else 'off'
        clicker_text = 'on' if clicker_enabled else 'off'
        capture_status_html = f"""<span style="color:white;">Triggerbot: </span><span style="color:{('#00ff48' if clicker_enabled else '#9c8dfd')};">{clicker_text}</span><span style="color:white;">\u200e \u200e \u200e Aimbot: </span><span style="color:{('#00ff48' if capture_enabled else '#9c8dfd')};">{capture_text}</span><span style="color:#272727;">\u200e \u200e \u200e\u200e  v1.10</span>"""
        self.capture_status_label.setText(capture_status_html)
        self.adjustSize()
        self.move(self.parent().width() - self.width() - 0, 390)

class DraggableOverlay(QWidget):

    def __init__(self, parent=None):
        super(DraggableOverlay, self).__init__(parent)
        self.setGeometry(0, 0, 65, 70)
        self.dragging = False
        self.drag_start_position = QPoint()
        self.setStyleSheet('background: transparent;')

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.dragging = True
            self.drag_start_position = event.globalPos() - self.parentWidget().frameGeometry().topLeft()
            event.accept()

    def mouseMoveEvent(self, event):
        if self.dragging:
            self.parentWidget().move(event.globalPos() - self.drag_start_position)
            event.accept()

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.LeftButton:
            self.dragging = False
            event.accept()

class MainWindow(QMainWindow):

    def __init__(self):
        super(MainWindow, self).__init__()
        self.browser = QWebEngineView()
        self.browser.setUrl(QUrl('http://127.0.0.1:54535/login'))
        self.setFixedSize(669, 420)
        self.setWindowFlags(self.windowFlags() | Qt.FramelessWindowHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        layout = QVBoxLayout()
        layout.setContentsMargins(0, 0, 0, 0)
        layout.addWidget(self.browser)
        container = QWidget()
        container.setLayout(layout)
        container.setStyleSheet('background: transparent;')
        self.setCentralWidget(container)
        self.show()
        self.draggable_overlay = DraggableOverlay(self)
        self.draggable_overlay.show()
        self.status_overlay = StatusOverlay(self)
        self.status_overlay.show()
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.check_status)
        self.timer.start(50)

    def check_status(self):
        current_capture_status = capture_enabled
        current_clicker_status = clicker_enabled
        if self.status_overlay.capture_status_label.text() != f'Capture Enabled: {current_capture_status}' or self.status_overlay.clicker_status_label.text() != f'Clicker Enabled: {current_clicker_status}':
            status_signal.status_changed.emit()

def run_flask():
    app.run(host='127.0.0.1', port=9999, debug=False)

def run_app():
    app = QApplication(sys.argv)
    window = MainWindow()
    sys.exit(app.exec_())
if __name__ == '__main__':
    hide_console()
    if is_admin():
        threading.Thread(target=run_flask).start()
        threading.Thread(target=capture_screen, daemon=True).start()
        run_app()
    else:
        threading.Thread(target=run_flask).start()
        threading.Thread(target=capture_screen, daemon=True).start()
        run_app()
