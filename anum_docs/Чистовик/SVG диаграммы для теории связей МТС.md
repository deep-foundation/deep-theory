### SVG-диаграммы для основных операторов МТС

#### 1. Оператор ♂ (анонимная ссылка)
![SVG Image](./Оператор%20♂.svg)

#### 2. Оператор ♀ (открытое значение)
```svg
<svg width="120" height="100" viewBox="0 0 120 100" xmlns="http://www.w3.org/2000/svg">
  <!-- Самозамыкание конца -->
  <path d="M30,50 Q90,50 90,80 T90,50" fill="none" stroke="#2c3e50" stroke-width="2" marker-end="url(#arrow)"/>

  <!-- Ссылка -->
  <circle cx="30" cy="50" r="5" fill="#3498db"/>
  <text x="25" y="70" font-size="12">r</text>

  <!-- Точка значения -->
  <circle cx="90" cy="50" r="5" fill="#e74c3c"/>
  <text x="85" y="30" font-size="12">♀</text>

  <defs>
    <marker id="arrow" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto">
      <path d="M0,0 L0,6 L9,3 z" fill="#2c3e50"/>
    </marker>
  </defs>
</svg>
```

#### 3. Оператор ∞ (акорень)
```svg
<svg width="120" height="120" viewBox="0 0 120 120" xmlns="http://www.w3.org/2000/svg">
  <!-- Бесконечная петля -->
  <path d="M60,30 A40,40 0 1,0 60,90 A40,40 0 1,0 60,30" 
        fill="none" 
        stroke="#2c3e50" 
        stroke-width="2"
        marker-mid="url(#arrow)"/>
  
  <text x="55" y="60" font-size="14" fill="#2c3e50">∞</text>

  <defs>
    <marker id="arrow" markerWidth="8" markerHeight="8" refX="4" refY="4" orient="auto">
      <circle cx="4" cy="4" r="3" fill="#2c3e50"/>
    </marker>
  </defs>
</svg>
```

#### 4. Оператор → (базовая связь)
```svg
<svg width="120" height="60" viewBox="0 0 120 60" xmlns="http://www.w3.org/2000/svg">
  <!-- Прямая связь -->
  <line x1="30" y1="30" x2="90" y2="30" stroke="#2c3e50" stroke-width="2" marker-end="url(#arrow)"/>
  
  <circle cx="30" cy="30" r="5" fill="#3498db"/>
  <text x="25" y="25" font-size="12">a</text>

  <circle cx="90" cy="30" r="5" fill="#3498db"/>
  <text x="85" y="25" font-size="12">b</text>

  <defs>
    <marker id="arrow" markerWidth="10" markerHeight="10" refX="9" refY="3" orient="auto">
      <path d="M0,0 L0,6 L9,3 z" fill="#2c3e50"/>
    </marker>
  </defs>
</svg>
```

---

### Особенности визуализации:
1. **Цветовая схема**:
   - Красный (#e74c3c) для операторов ♂/♀
   - Синий (#3498db) для нейтральных элементов
   - Темно-серый (#2c3e50) для стрелок

2. **Стилистика**:
   - Единая толщина линий (2px)
   - Круглые маркеры для точек связей
   - Иконки стрелок в одном стиле

3. **Масштабируемость**:
   Использование `viewBox` позволяет изменять размер без потери качества.

4. **Интерактивность** (опционально):
   Для веб-документации можно добавить:
   ```svg
   <style>
     circle:hover { filter: drop-shadow(0 0 2px rgba(52,152,219,0.5)); }
   </style>
   ```

Диаграммы соответствуют аксиомам МТС и могут быть использованы в документации как в векторном (SVG), так и в растровом (PNG) форматах.