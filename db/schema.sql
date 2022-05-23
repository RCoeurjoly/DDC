/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!40101 SET NAMES utf8mb4 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `fake`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `fake` (
  `exchange` char(8) NOT NULL,
  `segment_id` char(15) NOT NULL DEFAULT '',
  `subsegment_id` char(15) NOT NULL DEFAULT '',
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `rec_status` char(1) DEFAULT NULL,
  `segment_type` char(1) DEFAULT NULL,
  `name` char(50) DEFAULT NULL,
  PRIMARY KEY (`exchange`,`segment_id`,`subsegment_id`),
  KEY `segment_id` (`segment_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `grp`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `grp` (
  `exchange` char(8) NOT NULL,
  `segment_id` char(15) NOT NULL DEFAULT '',
  `subsegment_id` char(15) NOT NULL DEFAULT '',
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `rec_status` char(1) DEFAULT NULL,
  `segment_type` char(1) DEFAULT NULL,
  `name` char(50) DEFAULT NULL,
  PRIMARY KEY (`exchange`,`segment_id`,`subsegment_id`),
  KEY `segment_id` (`segment_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `grp_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `grp_deleted` (
  `exchange` char(8) NOT NULL,
  `segment_id` char(15) NOT NULL DEFAULT '',
  `subsegment_id` char(15) NOT NULL DEFAULT '',
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `rec_status` char(1) DEFAULT NULL,
  `segment_type` char(1) DEFAULT NULL,
  `name` char(50) DEFAULT NULL,
  PRIMARY KEY (`exchange`,`segment_id`,`subsegment_id`),
  KEY `segment_id` (`segment_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `grp_sty`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `grp_sty` (
  `exchange` char(8) NOT NULL,
  `segment_id` char(15) NOT NULL DEFAULT '',
  `subsegment_id` char(15) NOT NULL DEFAULT '',
  `vt_id` char(40) NOT NULL,
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `rec_status` char(1) DEFAULT NULL,
  `weighting` decimal(4,2) DEFAULT NULL,
  `position` int(11) DEFAULT NULL,
  PRIMARY KEY (`exchange`,`segment_id`,`subsegment_id`,`vt_id`),
  KEY `exc_vtid` (`exchange`,`vt_id`) USING BTREE,
  KEY `exc_chang` (`exchange`,`changed_time`) USING BTREE,
  KEY `exc_event` (`exchange`,`event_time`) USING BTREE,
  KEY `segment_id` (`segment_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `grp_sty_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `grp_sty_deleted` (
  `exchange` char(8) NOT NULL,
  `segment_id` char(15) NOT NULL DEFAULT '',
  `subsegment_id` char(15) NOT NULL DEFAULT '',
  `vt_id` char(40) NOT NULL,
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `rec_status` char(1) DEFAULT NULL,
  `weighting` decimal(4,2) DEFAULT NULL,
  `position` int(11) DEFAULT NULL,
  PRIMARY KEY (`exchange`,`segment_id`,`subsegment_id`,`vt_id`),
  KEY `exc_vtid` (`exchange`,`vt_id`) USING BTREE,
  KEY `exc_chang` (`exchange`,`changed_time`) USING BTREE,
  KEY `exc_event` (`exchange`,`event_time`) USING BTREE,
  KEY `segment_id` (`segment_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `historical_equity`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `historical_equity` (
  `MERCADO` varchar(5) NOT NULL DEFAULT 'M',
  `SIMBOLO` varchar(12) NOT NULL,
  `FECHA` date NOT NULL,
  `MONEDA` varchar(6) NOT NULL DEFAULT 'EUR',
  `PRECIO_REF` decimal(10,5) DEFAULT NULL,
  `PRECIO_APER` decimal(10,5) DEFAULT NULL,
  `PRECIO_CIERRE` decimal(10,5) DEFAULT NULL,
  `PRECIO_MIN` decimal(10,5) DEFAULT NULL,
  `PRECIO_MAX` decimal(10,5) DEFAULT NULL,
  `PRECIO_MED` decimal(10,5) DEFAULT NULL,
  `VOLUMEN` int(10) unsigned DEFAULT '0',
  `EFECTIVO` decimal(15,2) unsigned DEFAULT '0.00',
  `TMSTAMP` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `SHARES_FEED` bigint(20) unsigned DEFAULT '0',
  `SHARES_BOLETIN` bigint(20) unsigned DEFAULT '0',
  `SHARES_CIRC` bigint(20) unsigned DEFAULT '0',
  `VOLUMENBID` int(10) unsigned DEFAULT '0',
  `VOLUMENASK` int(10) unsigned DEFAULT '0',
  `TRDBID` int(6) unsigned DEFAULT '0',
  `TRDASK` int(6) unsigned DEFAULT '0',
  `TURNBID` decimal(15,2) unsigned DEFAULT '0.00',
  `TURNASK` decimal(15,2) unsigned DEFAULT '0.00',
  PRIMARY KEY (`FECHA`,`SIMBOLO`,`MERCADO`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `historical_fixed_income`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `historical_fixed_income` (
  `MERCADO` varchar(5) NOT NULL DEFAULT 'M',
  `SIMBOLO` varchar(12) NOT NULL,
  `FECHA` date NOT NULL,
  `MONEDA` varchar(6) NOT NULL DEFAULT '',
  `PRECIO_REF` decimal(10,5) DEFAULT NULL,
  `PRECIO_APER` decimal(10,5) DEFAULT NULL,
  `PRECIO_CIERRE` decimal(10,5) DEFAULT NULL,
  `PRECIO_MIN` decimal(10,5) DEFAULT NULL,
  `PRECIO_MAX` decimal(10,5) DEFAULT NULL,
  `PRECIO_MED` decimal(10,5) DEFAULT NULL,
  `VOLUMEN` int(10) unsigned DEFAULT '0',
  `EFECTIVO` decimal(15,2) unsigned DEFAULT '0.00',
  `TMSTAMP` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `SHARES_FEED` bigint(20) unsigned DEFAULT '0',
  `SHARES_BOLETIN` bigint(20) unsigned DEFAULT '0',
  `SHARES_CIRC` bigint(20) unsigned DEFAULT '0',
  `VOLUMENBID` int(10) unsigned DEFAULT '0',
  `VOLUMENASK` int(10) unsigned DEFAULT '0',
  `TRDBID` int(6) unsigned DEFAULT '0',
  `TRDASK` int(6) unsigned DEFAULT '0',
  `TURNBID` decimal(15,2) unsigned DEFAULT '0.00',
  `TURNASK` decimal(15,2) unsigned DEFAULT '0.00',
  `TIR_MED` decimal(10,5) DEFAULT NULL,
  `Cupon_corrido` decimal(10,5) DEFAULT NULL,
  `NOMINAL` decimal(13,5) DEFAULT NULL,
  PRIMARY KEY (`FECHA`,`SIMBOLO`,`MERCADO`,`MONEDA`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `ib_contratos`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `ib_contratos` (
  `isin` char(12) NOT NULL COMMENT 'codigo origen del producto',
  `ib_market` char(2) NOT NULL COMMENT 'codigo mercado ib',
  `prod_type` char(2) NOT NULL COMMENT 'futuro u opcion',
  `opcion_type` char(6) NOT NULL DEFAULT '' COMMENT 'put/ call',
  `ib_symbol` char(5) CHARACTER SET latin1 COLLATE latin1_general_cs NOT NULL COMMENT 'codigo valor ib',
  `open_interest_date` date DEFAULT NULL COMMENT 'fecha open interest',
  `last_trading_date` date DEFAULT NULL COMMENT 'ultimo dia de negociacion',
  `settlement_date` date DEFAULT NULL COMMENT 'fecha de precio de liquidacion',
  `expiry_date` date DEFAULT NULL COMMENT 'fecha de vencimiento',
  `delivery_date` date DEFAULT NULL COMMENT 'fecha de entrega',
  `delivery_month_code` char(1) DEFAULT NULL COMMENT 'codigo del mes de vencimiento',
  `strike_price` decimal(14,4) DEFAULT NULL COMMENT 'precio del ejercicio actual asociado al contrato derivado',
  `exercise_date` date DEFAULT NULL COMMENT 'fecha del ejercicio',
  `delivery_price` decimal(14,4) DEFAULT NULL COMMENT 'precio de liquidacion',
  `strike_price2` decimal(14,4) DEFAULT NULL COMMENT 'precio de ejercicio original,(en el momento de emision del contrato)',
  `contract_size` decimal(14,4) DEFAULT NULL COMMENT 'tamano de contrato',
  `tipo_liquidacion` char(1) DEFAULT NULL COMMENT 'tipo de liquidacion: Entraga subyacente/diferencia',
  `version_number` int(1) DEFAULT NULL COMMENT 'numero cambios que ha sufrido el precio ejercicio del contrato a lo largo de su existencia',
  `continuo` char(1) DEFAULT NULL COMMENT '0:No es continuo; 1: vencimiento 1; 2 vencimiento 2',
  `estilo` char(1) DEFAULT NULL COMMENT 'solo para opciones E(europeas) A (Americanas)',
  `rollover` char(1) DEFAULT NULL COMMENT 'indicar si es rollover(1) o no (0)',
  `codigo_contratacion` char(30) DEFAULT NULL COMMENT 'codigo de contratacion',
  `garantia` char(50) DEFAULT NULL COMMENT 'garantia o rango de garantia a aplicar',
  `garantiasadmisibles` char(100) DEFAULT NULL COMMENT 'garantias admisibles',
  PRIMARY KEY (`isin`,`ib_market`,`prod_type`,`opcion_type`,`ib_symbol`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `ib_mercado_valor`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `ib_mercado_valor` (
  `mercado` char(2) NOT NULL,
  `valor` char(5) CHARACTER SET latin1 COLLATE latin1_general_cs NOT NULL,
  `simbolo` char(32) DEFAULT NULL,
  `nombre_largo` varchar(256) DEFAULT NULL,
  `nombre_corto` varchar(128) DEFAULT NULL,
  `divisa` char(3) DEFAULT NULL,
  `divisa_ib` char(2) DEFAULT NULL,
  `isin` char(12) DEFAULT NULL,
  `quot_type` tinyint(4) DEFAULT NULL,
  `mic` char(4) NOT NULL,
  `orig_mic` char(4) DEFAULT NULL,
  `codigo_origen` varchar(50) NOT NULL,
  `created_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `event_time` timestamp NULL DEFAULT NULL,
  `inst_type` char(1) DEFAULT NULL,
  `inst_subtype` char(1) DEFAULT NULL,
  `fecha_expiracion` char(8) DEFAULT NULL,
  `prv_px` decimal(22,8) DEFAULT NULL,
  `prv_date` timestamp NULL DEFAULT NULL,
  `prv_yield` decimal(15,8) DEFAULT NULL,
  `tp_code` varchar(50) DEFAULT NULL,
  `settlement_px` decimal(22,8) DEFAULT NULL COMMENT 'precio de liquidacion',
  `alive` int(11) DEFAULT '1' COMMENT 'Si alive: 0 -> valor expirado, 1 -> valor vivo, 2 -> valor definitivamente expirado',
  PRIMARY KEY (`mercado`,`valor`),
  UNIQUE KEY `mic` (`mic`,`simbolo`,`divisa`),
  UNIQUE KEY `mercado_isin_divisa_orig` (`mercado`,`divisa`,`isin`,`orig_mic`),
  KEY `isin` (`isin`),
  KEY `mic_2` (`mic`,`simbolo`),
  KEY `mercado_time_event` (`mercado`,`event_time`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `ib_productos`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `ib_productos` (
  `ib_market` char(2) COLLATE latin1_general_cs NOT NULL COMMENT 'codigo mercado ib',
  `prod_type` char(2) COLLATE latin1_general_cs NOT NULL COMMENT 'futuro u opcion (F/O)',
  `isin_code` char(12) COLLATE latin1_general_cs NOT NULL COMMENT 'codigo origen del producto',
  `product_id` char(6) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'nemotecnico del producto',
  `cod_currency` char(3) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'divisa de emision',
  `prod_name` char(35) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'nombre del producto',
  `mkt_underly` char(2) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'codigo mercado ib del subyacente',
  `sym_underly` char(6) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'codigo valor ib del subyacente',
  `y_dmonth_list` char(12) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'codigo de vencimientos disponibles',
  `delivery_type` char(1) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'tipo de liquidacion: entrega subyacente/diferencia',
  `trading_hours` char(16) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'rango horario de negociacion',
  `daily_limit` char(10) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'rango de variacion del precio',
  `unit_daily_limit` char(12) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'unidades del rango de variacion',
  `warrants` char(50) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'codigo del subyacente segun fuente',
  `unit_of_trading` decimal(14,4) DEFAULT NULL COMMENT 'unidad de negociacion',
  `min_pri_mov` decimal(14,4) DEFAULT NULL COMMENT 'tamano tick: minimo movimiento del precio(tick)',
  `multiplier` decimal(14,4) DEFAULT NULL COMMENT 'multiplicador',
  `tick_value` decimal(14,4) DEFAULT NULL COMMENT 'valor monetario de un minimo movimiento del precio',
  `option_style_cod` char(12) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'estilo, para opciones : europeo/americanas',
  `expiry_exercise` date DEFAULT NULL COMMENT 'fecha de vencimiento',
  `strike_price_inc` decimal(14,4) DEFAULT NULL COMMENT 'incremento del precio ejercicio',
  `current_op_dates` char(100) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'vencimiento disponibles',
  `location` char(4) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'codigo mic del subyacente',
  `tipo_subyacente` char(2) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'tipo subyacente sobre el que se emite contrato:opciones sobre indices, materias primas',
  `unidad_cotiza` char(2) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'unidad cotizacion ib',
  `txt1_valor` char(4) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'para formar el codigo valor ib +secuencial',
  `txt2_nc` char(14) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'literal para el nombre corto',
  `txt3_nl` char(20) COLLATE latin1_general_cs DEFAULT NULL COMMENT 'literal para el nombre largo',
  PRIMARY KEY (`ib_market`,`prod_type`,`isin_code`),
  UNIQUE KEY `ib_market_txt1_valor` (`ib_market`,`txt1_valor`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1 COLLATE=latin1_general_cs;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `ib_warrants_datos_fijos`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `ib_warrants_datos_fijos` (
  `isin` char(12) NOT NULL COMMENT 'Isin',
  `mercado` char(2) NOT NULL COMMENT 'Mercado informado por la BMEMD',
  `codigoemision` char(8) CHARACTER SET latin1 COLLATE latin1_general_cs NOT NULL COMMENT 'Codigo de emision informado por BMEMD',
  `codigoemisora` char(4) DEFAULT NULL COMMENT 'Codigo de emisora',
  `tipo` char(1) DEFAULT NULL COMMENT 'Tipo de Warrant',
  `subtipo` char(1) DEFAULT NULL COMMENT 'Subtipo de Warrant',
  `nombrecortofuente` varchar(25) DEFAULT NULL COMMENT 'Nombre corto proporcionado por la fuente',
  `nombrelargofuente` varchar(120) DEFAULT NULL COMMENT 'Nombre largo proporcionado por la fuente',
  `nombrecortoib` varchar(45) DEFAULT NULL COMMENT 'Nombre corto Infobolsa',
  `nombrelargoib` varchar(120) DEFAULT NULL COMMENT 'Nombre largo Infobolsa',
  `categoria` char(1) DEFAULT NULL COMMENT 'Categoria del Warrant',
  `estilo` char(1) DEFAULT NULL COMMENT 'Estilo del Warrant',
  `divisa` char(3) NOT NULL COMMENT 'Divisa en la que cotiza el Warrant',
  `liquidaciontipo` char(1) DEFAULT NULL COMMENT 'Tipo de liquidacion',
  `subyacentetipo` char(2) DEFAULT NULL COMMENT 'Tipo de Subyacente',
  `subyacenteisin` char(12) DEFAULT NULL COMMENT 'Isin del subyacente',
  `fechaemision` date DEFAULT NULL COMMENT 'Fecha de emision',
  `primerdiacotizacion` char(8) DEFAULT NULL COMMENT 'Primer dia de cotizacion',
  `ultimodiacotizacion` char(8) DEFAULT NULL COMMENT 'Ultimo dia de cotizacion',
  `fechavencimiento` date DEFAULT NULL COMMENT 'Fecha de vencimiento',
  `fechavencimientocorta` char(6) DEFAULT NULL COMMENT 'Mes y anno de vencimiento',
  `strikeinicial` decimal(10,5) DEFAULT NULL COMMENT 'Precio de ejercicio inicial',
  `strike` decimal(10,5) DEFAULT NULL COMMENT 'Precio de ejercicio actual',
  `bonusprice` decimal(10,5) DEFAULT NULL COMMENT 'Bonus (aplica a bonus y bonus cap)',
  `barrera` decimal(10,5) DEFAULT NULL COMMENT 'Barrera (aplica a bonus y bonus cap)',
  `barreratocada` char(1) DEFAULT NULL COMMENT 'Barrera tocada (aplica a bonus y bonus cap)',
  `nivelsuperior` decimal(10,5) DEFAULT NULL COMMENT 'Nivel superior (aplica a discount + call?????)',
  `nivelinferior` decimal(10,5) DEFAULT NULL COMMENT 'Nivel inferior (aplica a discount + put?????)',
  `barreratocadafecha` char(8) DEFAULT NULL COMMENT 'Fecha barrera tocada (aplica a bonus, bonus cap y discount)',
  `barreraknockout` decimal(10,5) DEFAULT NULL COMMENT 'Barrera knock-out (aplica a turbo, turbo pro, sthigh, stlow)',
  `barrerakotocadafecha` char(8) DEFAULT NULL COMMENT 'Fecha knock-out (aplica a turbo, turbo pro, sthigh, stlow, inline)',
  `knockinsuperior` decimal(10,5) DEFAULT NULL COMMENT 'Knock-in superior (aplica a turbo pro)',
  `knockininferior` decimal(10,5) DEFAULT NULL COMMENT 'Knock-in inferior (aplica a turbo pro)',
  `fechaactivacion` char(8) DEFAULT NULL COMMENT 'Fecha activacion (aplica a turbo pro)',
  `knockoutsuperior` decimal(10,5) DEFAULT NULL COMMENT 'Barrera knock-out superior (aplica a inline)',
  `knockoutinferior` decimal(10,5) DEFAULT NULL COMMENT 'Barrera knock-out inferior (aplica a inline)',
  `ratio` decimal(10,5) DEFAULT NULL COMMENT 'Ratio',
  `paridad` decimal(10,5) DEFAULT NULL COMMENT 'Paridad',
  `numerowarrants` decimal(10,5) DEFAULT NULL COMMENT 'Num de warrants',
  `volumenminimo` bigint(10) DEFAULT NULL COMMENT 'Volumen minimo',
  `vencimientoautomatico` char(1) DEFAULT NULL COMMENT 'Perpetuo',
  `tamanocontrato` decimal(10,5) DEFAULT NULL COMMENT 'Tamanno del contrato',
  `negociacioncontinua` char(1) DEFAULT NULL COMMENT 'Negociacion continua',
  `plazanegociacion` char(1) DEFAULT NULL COMMENT 'Plaza negociacion	texto',
  `vencimientoanticipado` char(1) DEFAULT NULL COMMENT 'Indica si el warrant ha vencido anticipadamente (1) o no (0)',
  `estado` char(1) DEFAULT NULL COMMENT 'Estado en el que se encuentra el warrant',
  `apalancamiento` char(5) DEFAULT NULL COMMENT 'Para multi: apalancamiento del warrant',
  `payoutfijo` char(5) DEFAULT NULL COMMENT 'Para inline: pago a vencimiento',
  `nivelinverso` decimal(10,5) DEFAULT NULL COMMENT 'Para bonus inverso o bonus cap inverso',
  `fechaultimocambio` date DEFAULT NULL COMMENT 'Fecha del ultimo cambio de estado',
  `comentarios` varchar(300) DEFAULT NULL COMMENT 'Comentarios de las emisoras',
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `alive` int(11) DEFAULT '1' COMMENT 'Si alive: 0 -> valor expirado, 1 -> valor vivo, 2 -> valor definitivamente expirado',
  PRIMARY KEY (`mercado`,`codigoemision`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `ib_warrants_subyacentes`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `ib_warrants_subyacentes` (
  `isin` char(12) NOT NULL COMMENT 'Isin',
  `subyacenteisin` char(12) NOT NULL COMMENT 'Isin del subyacente',
  `tipo` char(2) DEFAULT NULL COMMENT 'Tipo del subyacente',
  `subtipo` char(1) DEFAULT NULL COMMENT 'Subtipo de Warrant',
  `mercadonombre` varchar(70) DEFAULT NULL COMMENT 'Nombre de la plaza de cotizacion',
  `simbolo` char(5) DEFAULT NULL COMMENT 'Simbolo subyacente	Texto',
  `divisa` char(3) DEFAULT NULL COMMENT 'Divisa subyacente',
  `nombrecorto` varchar(15) DEFAULT NULL COMMENT 'Nombre corto subyacente',
  `nombrelargo` varchar(25) DEFAULT NULL COMMENT 'Nombre largo subyacente',
  `mercadogestora` char(6) DEFAULT NULL COMMENT 'Codigo de mercado origen (Gestora)',
  `mercadovalorib` char(7) DEFAULT NULL COMMENT 'Mercado-valor de Infobolsa',
  `ric` char(15) DEFAULT NULL COMMENT 'RIC de infobolsa',
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `alive` int(11) DEFAULT '1' COMMENT 'Si alive: 0 -> valor expirado, 1 -> valor vivo, 2 -> valor definitivamente expirado',
  PRIMARY KEY (`isin`,`subyacenteisin`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `instrument`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `instrument` (
  `market_segment_id` int(11) NOT NULL DEFAULT '0',
  `security_id` varchar(32) NOT NULL COMMENT 'codigo isin del derivado',
  `event_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `security_id_source` char(1) NOT NULL DEFAULT '',
  `alt_security_id` int(11) DEFAULT NULL,
  `security_type` int(11) NOT NULL DEFAULT '0' COMMENT 'tipo de instrumento derivado',
  `security_subtype` int(11) NOT NULL,
  `product_complex` int(11) NOT NULL,
  `security_exchange` char(8) NOT NULL,
  `maturity_date` int(11) NOT NULL,
  `maturity_month_year` int(11) NOT NULL,
  `strike_price` char(32) DEFAULT NULL,
  `contract_multiplier` char(32) DEFAULT NULL,
  `put_or_call` int(11) NOT NULL,
  `opt_attribute` char(32) DEFAULT NULL,
  `exercise_style` int(11) NOT NULL,
  `orig_strike_price` char(32) DEFAULT NULL,
  `contract_generation_number` char(32) DEFAULT NULL,
  `transact_time` int(11) NOT NULL,
  `security_desc` char(64) NOT NULL COMMENT 'codigo del contrato',
  `security_name` char(255) DEFAULT NULL,
  `min_price_increment` char(32) DEFAULT NULL,
  `min_price_increment_amount` char(32) DEFAULT NULL,
  `security_status` char(32) DEFAULT NULL,
  `prev_adjusted_open_interest` bigint(20) NOT NULL,
  `prev_unadjusted_open_interest` bigint(20) NOT NULL,
  `prev_settl_px` char(32) DEFAULT NULL,
  `prev_close_px` char(32) DEFAULT NULL,
  `implied_market_indicator` int(10) unsigned NOT NULL DEFAULT '0',
  `multileg_model` int(11) NOT NULL,
  `price_range_rule_id` int(11) NOT NULL,
  `dayprv_close_prc_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `dayprv_tot_vol` decimal(12,0) DEFAULT NULL,
  `dayprv_tot_turn` decimal(15,3) DEFAULT NULL,
  `yearprv_close_prc` decimal(13,5) DEFAULT NULL,
  `year_low_prc` decimal(13,5) DEFAULT NULL,
  `year_low_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_high_prc` decimal(13,5) DEFAULT NULL,
  `year_high_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_tot_vol` decimal(12,0) DEFAULT NULL,
  `year_tot_turn` decimal(15,3) DEFAULT NULL,
  `grp_id` bigint(20) NOT NULL DEFAULT '0',
  `isin` char(12) DEFAULT NULL COMMENT 'codigo isin del derivado',
  `mic` char(4) DEFAULT NULL COMMENT 'codigo mic del derivado',
  `cfi` char(6) DEFAULT NULL COMMENT 'codigo cfi del derivado',
  `ccy` char(3) DEFAULT NULL COMMENT 'moneda del derivado',
  `max_trade_vol` decimal(22,8) DEFAULT NULL COMMENT 'volumen maximo negociado',
  `min_trade_vol` decimal(22,8) DEFAULT NULL COMMENT 'volumen minimo negociado',
  `round_lot` decimal(22,8) DEFAULT NULL COMMENT 'round_lot',
  `entitlement_id` int(11) DEFAULT NULL COMMENT 'Entitlement ID',
  `ccy_precision` char(1) DEFAULT NULL COMMENT 'Currency Precision',
  PRIMARY KEY (`security_exchange`,`market_segment_id`,`security_id`),
  UNIQUE KEY `exc_sec_desc` (`security_exchange`,`security_desc`),
  KEY `maturity_date` (`security_exchange`,`maturity_date`) USING BTREE,
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_chang` (`security_exchange`,`changed_time`) USING BTREE,
  KEY `exc_event` (`security_exchange`,`event_time`) USING BTREE,
  KEY `exc_isin` (`security_exchange`,`isin`) USING BTREE,
  KEY `security_id` (`security_id`),
  KEY `idx_isin` (`isin`),
  KEY `idx_mic_sym_ccy` (`mic`,`security_id`,`ccy`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `instrument_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `instrument_deleted` (
  `market_segment_id` int(11) NOT NULL DEFAULT '0',
  `security_id` varchar(32) NOT NULL COMMENT 'codigo isin del derivado',
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `security_id_source` char(1) NOT NULL DEFAULT '',
  `alt_security_id` int(11) DEFAULT NULL,
  `security_type` int(11) NOT NULL DEFAULT '0' COMMENT 'tipo de instrumento derivado',
  `security_subtype` int(11) NOT NULL,
  `product_complex` int(11) NOT NULL,
  `security_exchange` char(8) NOT NULL,
  `maturity_date` int(11) NOT NULL,
  `maturity_month_year` int(11) NOT NULL,
  `strike_price` char(32) DEFAULT NULL,
  `contract_multiplier` char(32) DEFAULT NULL,
  `put_or_call` int(11) NOT NULL,
  `opt_attribute` char(32) DEFAULT NULL,
  `exercise_style` int(11) NOT NULL,
  `orig_strike_price` char(32) DEFAULT NULL,
  `contract_generation_number` char(32) DEFAULT NULL,
  `transact_time` int(11) NOT NULL,
  `security_desc` char(64) NOT NULL COMMENT 'codigo del contrato',
  `security_name` char(150) DEFAULT NULL,
  `min_price_increment` char(32) DEFAULT NULL,
  `min_price_increment_amount` char(32) DEFAULT NULL,
  `security_status` char(32) DEFAULT NULL,
  `prev_adjusted_open_interest` bigint(20) NOT NULL,
  `prev_unadjusted_open_interest` bigint(20) NOT NULL,
  `prev_settl_px` char(32) DEFAULT NULL,
  `prev_close_px` char(32) DEFAULT NULL,
  `implied_market_indicator` int(10) unsigned NOT NULL DEFAULT '0',
  `multileg_model` int(11) NOT NULL,
  `price_range_rule_id` int(11) NOT NULL,
  `dayprv_close_prc_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `dayprv_tot_vol` decimal(12,0) DEFAULT NULL,
  `dayprv_tot_turn` decimal(15,3) DEFAULT NULL,
  `yearprv_close_prc` decimal(13,5) DEFAULT NULL,
  `year_low_prc` decimal(13,5) DEFAULT NULL,
  `year_low_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_high_prc` decimal(13,5) DEFAULT NULL,
  `year_high_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_tot_vol` decimal(12,0) DEFAULT NULL,
  `year_tot_turn` decimal(15,3) DEFAULT NULL,
  `grp_id` bigint(20) NOT NULL DEFAULT '0',
  `isin` char(12) DEFAULT NULL COMMENT 'codigo isin del derivado',
  `mic` char(4) DEFAULT NULL COMMENT 'codigo mic del derivado',
  `cfi` char(6) DEFAULT NULL COMMENT 'codigo cfi del derivado',
  `ccy` char(3) DEFAULT NULL COMMENT 'moneda del derivado',
  `max_trade_vol` decimal(22,8) DEFAULT NULL COMMENT 'volumen maximo negociado',
  `min_trade_vol` decimal(22,8) DEFAULT NULL COMMENT 'volumen minimo negociado',
  `round_lot` decimal(22,8) DEFAULT NULL COMMENT 'round_lot',
  `entitlement_id` int(11) DEFAULT NULL COMMENT 'Entitlement ID',
  `ccy_precision` char(1) DEFAULT NULL COMMENT 'Currency Precision',
  PRIMARY KEY (`security_exchange`,`market_segment_id`,`security_id`),
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_chang` (`security_exchange`,`changed_time`) USING BTREE,
  KEY `exc_isin` (`security_exchange`,`isin`) USING BTREE,
  KEY `maturity_date` (`security_exchange`,`maturity_date`) USING BTREE,
  KEY `exc_event` (`security_exchange`,`event_time`) USING BTREE,
  KEY `security_id` (`security_id`),
  KEY `exc_sec_desc` (`security_exchange`,`security_desc`),
  KEY `idx_mic_event` (`mic`,`event_time`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `instrument_history`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `instrument_history` (
  `security_exchange` char(8) DEFAULT NULL,
  `market_segment_id` int(11) DEFAULT NULL,
  `security_id` bigint(20) DEFAULT NULL,
  `service` varchar(100) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `comments` text,
  KEY `exc_market_segment_id_new` (`market_segment_id`,`security_id`),
  KEY `sec_exc_sec_id` (`security_exchange`,`security_id`),
  KEY `event` (`event_time`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `leg`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `leg` (
  `security_exchange` char(8) NOT NULL,
  `security_id` char(32) NOT NULL DEFAULT '0',
  `leg_security_id` char(32) NOT NULL DEFAULT '0',
  `event_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `leg_side` int(11) DEFAULT NULL COMMENT 'Lado de la pata',
  `leg_ratio_quantity` int(11) DEFAULT NULL COMMENT 'Ratio o cantidad de la pata',
  `leg_price` decimal(18,8) DEFAULT NULL COMMENT 'Precio de la pata',
  PRIMARY KEY (`security_exchange`,`security_id`,`leg_security_id`),
  KEY `leg_security_leg` (`security_exchange`,`leg_security_id`) USING BTREE,
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_chang` (`security_exchange`,`changed_time`) USING BTREE,
  KEY `exc_event` (`security_exchange`,`event_time`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `leg_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `leg_deleted` (
  `security_exchange` char(8) NOT NULL,
  `security_id` char(32) NOT NULL DEFAULT '0',
  `leg_security_id` char(32) NOT NULL DEFAULT '0',
  `event_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `leg_side` int(11) DEFAULT NULL COMMENT 'Lado de la pata',
  `leg_ratio_quantity` int(11) DEFAULT NULL COMMENT 'Ratio o cantidad de la pata',
  `leg_price` decimal(18,8) DEFAULT NULL COMMENT 'Precio de la pata',
  PRIMARY KEY (`security_exchange`,`security_id`,`leg_security_id`),
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_chang` (`security_exchange`,`changed_time`) USING BTREE,
  KEY `exc_event` (`security_exchange`,`event_time`) USING BTREE,
  KEY `leg_security_leg` (`security_exchange`,`leg_security_id`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `leg_history`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `leg_history` (
  `security_exchange` char(8) NOT NULL,
  `security_id` char(32) NOT NULL COMMENT 'identificador del contrato asociado a esta pata',
  `leg_security_id_old` char(32) DEFAULT NULL,
  `leg_security_id_new` char(32) DEFAULT NULL,
  `service` varchar(100) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `comments` text,
  KEY `exc_market_segment_id_new` (`security_exchange`,`security_id`,`leg_security_id_new`),
  KEY `exc_market_segment_id_old` (`security_exchange`,`security_id`,`leg_security_id_old`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `margininfo_instrument`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `margininfo_instrument` (
  `security_exchange` char(4) NOT NULL,
  `instrument` char(64) NOT NULL,
  `currency` char(3) NOT NULL,
  `udlying_security_exchange` char(4) DEFAULT NULL,
  `udlying_symbol` char(48) DEFAULT NULL,
  `udlying_currency` char(3) DEFAULT NULL,
  `theo_prc` char(255) NOT NULL DEFAULT '',
  `gp_theo_prc` char(64) NOT NULL DEFAULT '',
  `deltas` char(255) NOT NULL DEFAULT '',
  `gp_deltas` char(64) NOT NULL DEFAULT '',
  `num_scenarios` int(11) DEFAULT NULL,
  `settlement_date` date DEFAULT NULL,
  `close_prc` double DEFAULT NULL,
  `event_time` timestamp NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`security_exchange`,`instrument`,`currency`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `margininfo_udlying`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `margininfo_udlying` (
  `security_exchange` char(4) NOT NULL,
  `symbol` char(48) NOT NULL,
  `currency` char(3) NOT NULL,
  `min_spread` double NOT NULL DEFAULT '0',
  `spread_factor` double NOT NULL DEFAULT '0',
  `great_position_perc` char(32) NOT NULL DEFAULT '',
  `event_time` timestamp NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`security_exchange`,`symbol`,`currency`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `nodes`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `nodes` (
  `node_id` int(10) unsigned DEFAULT NULL,
  `parent_node_id` int(10) unsigned DEFAULT NULL,
  `birth_order` int(10) unsigned DEFAULT NULL,
  `function_name` blob NOT NULL,
  `return_value` blob NOT NULL,
  `object_on_entry` blob NOT NULL,
  `object_when_returning` blob NOT NULL,
  `creation_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `finishing_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00' ON UPDATE CURRENT_TIMESTAMP,
  UNIQUE KEY `node_id` (`node_id`),
  UNIQUE KEY `parent_node_id` (`parent_node_id`,`birth_order`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `optiq_decimals`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `optiq_decimals` (
  `exchange` char(8) NOT NULL,
  `vt_id` char(40) NOT NULL,
  `ticker_plant_code` int(11) NOT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `px_decimals` int(11) DEFAULT '0',
  `qty_decimals` int(11) DEFAULT '0',
  `amnt_decimals` int(11) DEFAULT '0',
  `ratio_decimals` int(11) DEFAULT '0',
  `strike_px_decimals` int(11) DEFAULT '0',
  `issue_px_decimals` int(11) DEFAULT '0',
  `qty_max_decimals` int(11) DEFAULT '0',
  `optiq_segment` int(11) DEFAULT NULL,
  `partit` int(11) DEFAULT NULL,
  `trading_id` int(11) NOT NULL COMMENT 'Security Trading ID',
  PRIMARY KEY (`exchange`,`vt_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `product`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `product` (
  `market_id` char(8) NOT NULL,
  `market_segment_id` int(11) NOT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `trade_date` int(11) NOT NULL,
  `market_segment` char(32) NOT NULL,
  `market_segment_desc` char(255) NOT NULL COMMENT 'Descripcion del producto',
  `market_segment_symbol` char(32) NOT NULL,
  `parent_mkt_segm_id` char(50) NOT NULL,
  `currency` char(32) NOT NULL,
  `market_segment_status` int(11) NOT NULL DEFAULT '0',
  `us_firm_flag` int(11) NOT NULL,
  `partition_id` int(11) NOT NULL,
  `underlying_security_exchange` char(8) NOT NULL,
  `underlying_security` char(32) NOT NULL,
  `underlying_id` char(32) NOT NULL,
  `underlying_last_px` char(32) NOT NULL DEFAULT '0.00000000',
  `ref_market_segment_id` int(11) NOT NULL DEFAULT '0',
  `quote_side_indicator` int(11) NOT NULL DEFAULT '0',
  `price_range_fast_market_factor` char(32) DEFAULT NULL,
  PRIMARY KEY (`market_id`,`market_segment_id`),
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_chang` (`market_id`,`changed_time`) USING BTREE,
  KEY `exc_event` (`market_id`,`event_time`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `product_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `product_deleted` (
  `market_id` char(8) NOT NULL,
  `market_segment_id` int(11) NOT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `trade_date` int(11) NOT NULL,
  `market_segment` char(32) NOT NULL,
  `market_segment_desc` char(100) NOT NULL COMMENT 'Descripcion del producto',
  `market_segment_symbol` char(32) NOT NULL,
  `parent_mkt_segm_id` char(32) NOT NULL,
  `currency` char(32) NOT NULL,
  `market_segment_status` int(11) NOT NULL DEFAULT '0',
  `us_firm_flag` int(11) NOT NULL,
  `partition_id` int(11) NOT NULL,
  `underlying_security_exchange` char(8) NOT NULL,
  `underlying_security` char(32) NOT NULL,
  `underlying_id` char(32) NOT NULL,
  `underlying_last_px` char(32) NOT NULL DEFAULT '0.00000000',
  `ref_market_segment_id` int(11) NOT NULL DEFAULT '0',
  `quote_side_indicator` int(11) NOT NULL DEFAULT '0',
  `price_range_fast_market_factor` char(32) DEFAULT NULL,
  PRIMARY KEY (`market_id`,`market_segment_id`),
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_chang` (`market_id`,`changed_time`) USING BTREE,
  KEY `exc_event` (`market_id`,`event_time`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `product_history`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `product_history` (
  `market_id` char(8) DEFAULT NULL,
  `market_segment_id_old` char(32) DEFAULT NULL,
  `market_segment_id_new` char(32) DEFAULT NULL,
  `market_segment_symbol_old` varchar(12) DEFAULT NULL,
  `market_segment_symbol_new` varchar(12) DEFAULT NULL,
  `service` varchar(100) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `comments` text,
  KEY `exc_market_segment_id_new` (`market_id`,`market_segment_id_new`),
  KEY `exc_market_segment_id_old` (`market_id`,`market_segment_id_old`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_aux_security`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_aux_security` (
  `id` bigint(20) unsigned NOT NULL AUTO_INCREMENT,
  `mic` char(4) NOT NULL,
  `symbol` varchar(64) NOT NULL,
  `currency` char(3) NOT NULL,
  PRIMARY KEY (`id`),
  UNIQUE KEY `mic` (`mic`,`symbol`,`currency`)
) ENGINE=MyISAM AUTO_INCREMENT=4294967296 DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_leg`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_leg` (
  `mic` char(4) NOT NULL,
  `low_internal_code` bigint(11) NOT NULL,
  `leg_internal_code` int(11) NOT NULL,
  `ratio` decimal(18,8) DEFAULT NULL,
  `side` int(11) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`mic`,`low_internal_code`,`leg_internal_code`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_market`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_market` (
  `mic` char(4) NOT NULL,
  `cfi` char(6) NOT NULL,
  `market_id` int(11) DEFAULT NULL,
  `descrp` varchar(100) DEFAULT NULL,
  `timezone` varchar(100) DEFAULT NULL,
  `country` char(3) DEFAULT NULL,
  `num_instr` int(11) DEFAULT NULL,
  `request_stys` char(1) DEFAULT 'N',
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `last_request` char(24) DEFAULT NULL,
  PRIMARY KEY (`mic`,`cfi`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_product`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_product` (
  `mic` char(4) NOT NULL COMMENT 'Codigo mic del producto',
  `id` int(11) NOT NULL AUTO_INCREMENT COMMENT 'Identificador del producto auto_increment',
  `name` varchar(100) NOT NULL COMMENT 'Nombre del grupo',
  PRIMARY KEY (`id`),
  UNIQUE KEY `mic` (`mic`,`name`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_security`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_security` (
  `internal_code` char(32) NOT NULL,
  `low_internal_code` bigint(11) NOT NULL,
  `mic` char(4) NOT NULL,
  `internal_mic` int(11) NOT NULL,
  `vt_exchange` char(4) DEFAULT NULL,
  `cfi` char(6) NOT NULL,
  `orig_mic` char(4) DEFAULT NULL,
  `internal_orig_mic` int(11) DEFAULT NULL,
  `symbol` char(64) DEFAULT NULL,
  `isin` char(12) DEFAULT NULL,
  `sedol` char(7) DEFAULT NULL,
  `ric` char(15) DEFAULT NULL,
  `telekurs_valor` varchar(32) DEFAULT NULL,
  `local_code` char(64) DEFAULT NULL,
  `description` char(255) DEFAULT NULL,
  `currency` char(8) DEFAULT NULL,
  `country` char(8) DEFAULT NULL,
  `lot_size` char(16) DEFAULT NULL,
  `tick_size` char(16) DEFAULT NULL,
  `mat_year` int(11) DEFAULT NULL,
  `mat_month` int(11) DEFAULT NULL,
  `mat_day` int(11) DEFAULT NULL,
  `contract_version` int(11) DEFAULT NULL,
  `product_id` int(11) DEFAULT NULL,
  `product_symbol` varchar(32) DEFAULT NULL,
  `contract_symbol` varchar(50) DEFAULT NULL,
  `product_complex` varchar(50) DEFAULT NULL,
  `nb_legs` int(11) DEFAULT NULL,
  `lse_sector` char(32) DEFAULT NULL,
  `lse_segment` char(32) DEFAULT NULL,
  `lse_mark_size` decimal(18,8) DEFAULT NULL,
  `creation_time` char(24) DEFAULT NULL,
  `modif_time` char(24) DEFAULT NULL,
  `dead` char(1) DEFAULT 'N',
  `tick_table` int(11) DEFAULT NULL,
  `strike_price` decimal(18,8) DEFAULT NULL,
  `contract_mult` decimal(18,8) DEFAULT NULL,
  `security_type` char(32) DEFAULT NULL,
  `security_subtype` char(50) DEFAULT NULL,
  `internal_source_id` int(11) DEFAULT NULL,
  `issuer` char(120) DEFAULT NULL,
  `min_trade_vol` decimal(18,8) DEFAULT NULL,
  `market_segment_id` char(32) DEFAULT NULL,
  `market_segment_desc` char(100) DEFAULT NULL,
  `prv_close_prc` decimal(18,5) DEFAULT NULL,
  `prv_close_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `price_type` int(11) DEFAULT NULL,
  `dated_date` date DEFAULT NULL,
  `swx_issuer_country` varchar(32) DEFAULT NULL,
  `swx_trading_sess_id` varchar(32) DEFAULT NULL,
  `swx_listing_state_desc` varchar(32) DEFAULT NULL,
  `coupon_rate` decimal(18,8) DEFAULT NULL,
  `factor` decimal(18,8) DEFAULT NULL,
  `std_maturity` varchar(8) DEFAULT NULL,
  `strike_currency` varchar(8) DEFAULT NULL,
  `underlying_local_code` varchar(32) DEFAULT NULL,
  `dynamic_variation_range` decimal(18,8) DEFAULT NULL,
  `static_variation_range` decimal(18,8) DEFAULT NULL,
  `bloomberg_code` varchar(32) DEFAULT NULL,
  `figi_code` varchar(32) DEFAULT NULL,
  `delayed_feed_min` int(11) DEFAULT NULL,
  `internal_entitlement_id` int(11) DEFAULT NULL,
  `security_trading_id` varchar(32) DEFAULT NULL,
  `mbl_layers_desc` varchar(8) DEFAULT NULL,
  `operating_mic` char(4) DEFAULT NULL,
  `security_status` int(11) DEFAULT NULL,
  `security_group` varchar(16) DEFAULT NULL,
  `udly_symb` varchar(32) DEFAULT NULL,
  `udly_isin` char(12) DEFAULT NULL,
  `udly_mic` varchar(4) DEFAULT NULL,
  `udly_id` int(11) DEFAULT NULL,
  `segment_mic` char(4) DEFAULT NULL,
  `face_value` decimal(18,8) DEFAULT NULL,
  `coupon_payment_date` date DEFAULT NULL,
  `issue_date` date DEFAULT NULL,
  `ccp_eligible` tinyint(1) DEFAULT NULL,
  `settl_period` int(11) DEFAULT NULL,
  `prc_display_prec` int(11) DEFAULT NULL,
  `swx_list_state_code` varchar(32) DEFAULT NULL,
  `contract_isin` varchar(12) DEFAULT NULL,
  `product_complex_type` int(11) DEFAULT NULL,
  `original_strike_price` decimal(18,8) DEFAULT NULL,
  `outstanding_shares` bigint(20) DEFAULT NULL COMMENT 'numero de acciones',
  `bme_maturity_date` date DEFAULT NULL,
  `created_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`internal_code`),
  UNIQUE KEY `low_internal_code` (`low_internal_code`),
  UNIQUE KEY `mic_2` (`mic`,`symbol`,`currency`),
  KEY `mic` (`mic`,`cfi`),
  KEY `vt_exchange` (`vt_exchange`),
  KEY `mic_event_time` (`mic`,`event_time`) USING BTREE,
  KEY `mic_maturity_date` (`mic`,`bme_maturity_date`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_security_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_security_deleted` (
  `internal_code` char(32) NOT NULL,
  `low_internal_code` bigint(11) NOT NULL,
  `mic` char(4) NOT NULL,
  `internal_mic` int(11) NOT NULL,
  `vt_exchange` char(4) DEFAULT NULL,
  `cfi` char(6) NOT NULL,
  `orig_mic` char(4) DEFAULT NULL,
  `internal_orig_mic` int(11) DEFAULT NULL,
  `symbol` char(64) DEFAULT NULL,
  `isin` char(12) DEFAULT NULL,
  `sedol` char(7) DEFAULT NULL,
  `ric` char(15) DEFAULT NULL,
  `telekurs_valor` varchar(32) DEFAULT NULL,
  `local_code` char(64) DEFAULT NULL,
  `description` char(255) DEFAULT NULL,
  `currency` char(8) DEFAULT NULL,
  `country` char(8) DEFAULT NULL,
  `lot_size` char(16) DEFAULT NULL,
  `tick_size` char(16) DEFAULT NULL,
  `mat_year` int(11) DEFAULT NULL,
  `mat_month` int(11) DEFAULT NULL,
  `mat_day` int(11) DEFAULT NULL,
  `contract_version` int(11) DEFAULT NULL,
  `product_id` int(11) DEFAULT NULL,
  `product_symbol` varchar(32) DEFAULT NULL,
  `contract_symbol` varchar(50) DEFAULT NULL,
  `product_complex` varchar(50) DEFAULT NULL,
  `nb_legs` int(11) DEFAULT NULL,
  `lse_sector` char(32) DEFAULT NULL,
  `lse_segment` char(32) DEFAULT NULL,
  `lse_mark_size` decimal(18,8) DEFAULT NULL,
  `creation_time` char(24) DEFAULT NULL,
  `modif_time` char(24) DEFAULT NULL,
  `dead` char(1) DEFAULT 'N',
  `tick_table` int(11) DEFAULT NULL,
  `strike_price` decimal(18,8) DEFAULT NULL,
  `contract_mult` decimal(18,8) DEFAULT NULL,
  `security_type` char(32) DEFAULT NULL,
  `security_subtype` char(50) DEFAULT NULL,
  `internal_source_id` int(11) DEFAULT NULL,
  `issuer` char(120) DEFAULT NULL,
  `min_trade_vol` decimal(18,8) DEFAULT NULL,
  `market_segment_id` char(32) DEFAULT NULL,
  `market_segment_desc` char(100) DEFAULT NULL,
  `prv_close_prc` decimal(18,5) DEFAULT NULL,
  `prv_close_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `price_type` int(11) DEFAULT NULL,
  `dated_date` date DEFAULT NULL,
  `swx_issuer_country` varchar(32) DEFAULT NULL,
  `swx_trading_sess_id` varchar(32) DEFAULT NULL,
  `swx_listing_state_desc` varchar(32) DEFAULT NULL,
  `coupon_rate` decimal(18,8) DEFAULT NULL,
  `factor` decimal(18,8) DEFAULT NULL,
  `std_maturity` varchar(8) DEFAULT NULL,
  `strike_currency` varchar(8) DEFAULT NULL,
  `underlying_local_code` varchar(32) DEFAULT NULL,
  `dynamic_variation_range` decimal(18,8) DEFAULT NULL,
  `static_variation_range` decimal(18,8) DEFAULT NULL,
  `bloomberg_code` varchar(32) DEFAULT NULL,
  `figi_code` varchar(32) DEFAULT NULL,
  `delayed_feed_min` int(11) DEFAULT NULL,
  `internal_entitlement_id` int(11) DEFAULT NULL,
  `security_trading_id` varchar(32) DEFAULT NULL,
  `mbl_layers_desc` varchar(8) DEFAULT NULL,
  `operating_mic` char(4) DEFAULT NULL,
  `security_status` int(11) DEFAULT NULL,
  `security_group` varchar(16) DEFAULT NULL,
  `udly_symb` varchar(32) DEFAULT NULL,
  `udly_isin` char(12) DEFAULT NULL,
  `udly_mic` varchar(4) DEFAULT NULL,
  `udly_id` int(11) DEFAULT NULL,
  `segment_mic` char(4) DEFAULT NULL,
  `face_value` decimal(18,8) DEFAULT NULL,
  `coupon_payment_date` date DEFAULT NULL,
  `issue_date` date DEFAULT NULL,
  `ccp_eligible` tinyint(1) DEFAULT NULL,
  `settl_period` int(11) DEFAULT NULL,
  `prc_display_prec` int(11) DEFAULT NULL,
  `swx_list_state_code` varchar(32) DEFAULT NULL,
  `contract_isin` varchar(12) DEFAULT NULL,
  `product_complex_type` int(11) DEFAULT NULL,
  `original_strike_price` decimal(18,8) DEFAULT NULL,
  `outstanding_shares` bigint(20) DEFAULT NULL COMMENT 'numero de acciones',
  `bme_maturity_date` date DEFAULT NULL,
  `created_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  KEY `mic` (`mic`,`cfi`) USING BTREE,
  KEY `mic_event_time` (`mic`,`event_time`) USING BTREE,
  KEY `mic_maturity_date` (`mic`,`bme_maturity_date`) USING BTREE
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `quant_tick_tables`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `quant_tick_tables` (
  `table_id` int(11) NOT NULL,
  `low` decimal(18,8) NOT NULL,
  `high` decimal(18,8) NOT NULL,
  `tick` decimal(18,8) NOT NULL,
  PRIMARY KEY (`table_id`,`low`,`high`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `repo_udly`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `repo_udly` (
  `exchange` varchar(8) NOT NULL,
  `vt_id` varchar(40) NOT NULL,
  `repo_type` varchar(40) NOT NULL,
  `udly_symbol` varchar(40) NOT NULL,
  `udly_exchange` varchar(8) NOT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  PRIMARY KEY (`exchange`,`vt_id`,`repo_type`,`udly_symbol`),
  KEY `udly_symbol` (`udly_symbol`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `schema_migrations`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `schema_migrations` (
  `version` varchar(255) COLLATE latin1_bin NOT NULL,
  PRIMARY KEY (`version`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1 COLLATE=latin1_bin;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `security`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `security` (
  `exchange` char(8) NOT NULL,
  `vt_id` char(40) NOT NULL,
  `ticker` char(48) NOT NULL,
  `isin` char(12) DEFAULT NULL,
  `sedol` char(7) DEFAULT NULL,
  `cusip` char(9) DEFAULT NULL,
  `local_code` char(9) DEFAULT NULL,
  `ticker_plant_code` char(32) DEFAULT NULL,
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `inst_status_type` char(1) DEFAULT NULL,
  `ticker_plant_flag` char(1) DEFAULT NULL,
  `subexchange` char(8) DEFAULT NULL,
  `inst_type` char(1) DEFAULT NULL,
  `inst_subtype` char(1) DEFAULT NULL,
  `name` char(255) DEFAULT NULL,
  `country` char(3) DEFAULT NULL,
  `issue_amount` decimal(22,8) DEFAULT NULL,
  `issue_price` decimal(22,8) DEFAULT NULL,
  `issue_date` date DEFAULT NULL,
  `issuer_code` char(8) DEFAULT NULL,
  `quotation_type` char(1) DEFAULT NULL,
  `currency` char(3) DEFAULT NULL,
  `currency_precision` char(1) DEFAULT NULL,
  `lot_size` int(11) DEFAULT NULL,
  `tick_size` decimal(12,8) DEFAULT NULL,
  `closing_date` date DEFAULT NULL,
  `closing_date_type` char(1) DEFAULT NULL,
  `thr_sta_perc` decimal(5,2) DEFAULT NULL,
  `thr_sta_low_prc` decimal(19,5) DEFAULT NULL,
  `thr_sta_high_prc` decimal(19,5) DEFAULT NULL,
  `thr_dyn_perc` decimal(5,2) DEFAULT NULL,
  `thr_dyn_low_prc` decimal(19,5) DEFAULT NULL,
  `thr_dyn_high_prc` decimal(19,5) DEFAULT NULL,
  `exercise_prc` decimal(15,8) DEFAULT NULL,
  `exercise_date` date DEFAULT NULL COMMENT 'fecha de ejercicio',
  `contract_multiplier` decimal(19,9) DEFAULT NULL,
  `udlying_id` char(32) DEFAULT NULL,
  `udlying_isin` char(12) DEFAULT NULL,
  `udlying_type` char(3) DEFAULT NULL,
  `dayprv_close_prc` decimal(19,5) DEFAULT NULL,
  `dayprv_close_yield` decimal(15,8) DEFAULT NULL,
  `dayprv_close_prc_type` char(1) DEFAULT NULL,
  `dayprv_close_prc_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `dayprv_tot_vol` decimal(12,0) DEFAULT NULL,
  `dayprv_tot_turn` decimal(22,3) DEFAULT NULL,
  `yearprv_close_prc` decimal(19,5) DEFAULT NULL,
  `year_low_prc` decimal(19,5) DEFAULT NULL,
  `year_low_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_high_prc` decimal(19,5) DEFAULT NULL,
  `year_high_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_tot_vol` decimal(12,0) DEFAULT NULL,
  `year_tot_turn` decimal(22,3) DEFAULT NULL,
  `data_source` char(2) DEFAULT NULL,
  `cfi` char(6) DEFAULT NULL,
  `ric` char(15) DEFAULT NULL,
  `mic` char(4) DEFAULT NULL,
  `real_mic` char(4) DEFAULT 'NONE',
  `barrier_prc` decimal(13,5) DEFAULT NULL,
  `war_type` char(1) DEFAULT NULL,
  `wkn_no` char(9) DEFAULT NULL,
  `tick_table` int(11) DEFAULT NULL,
  `nav` decimal(18,8) DEFAULT NULL,
  `nav_date` date DEFAULT NULL,
  `owner_member` int(11) DEFAULT NULL,
  `clearer_member` int(11) DEFAULT NULL,
  `product_type` varchar(2) DEFAULT NULL,
  `coupon_period` char(1) DEFAULT NULL,
  `coupon_type` char(1) DEFAULT NULL,
  `coupon_next_date` date DEFAULT NULL,
  `payment_type` char(1) DEFAULT NULL,
  `quotation_modality` char(1) DEFAULT NULL,
  `perpetual_ind` char(1) DEFAULT NULL,
  `interest_rate` decimal(13,5) DEFAULT NULL,
  `next_amortization_date` date DEFAULT NULL,
  `accrued_interest` decimal(13,6) DEFAULT NULL,
  `low_barrier_prc` decimal(13,5) DEFAULT NULL,
  `high_barrier_prc` decimal(13,5) DEFAULT NULL,
  `first_trading_date` date DEFAULT NULL,
  `last_trading_date` date DEFAULT NULL,
  `fee_type` char(2) DEFAULT NULL,
  `trading_scope` char(1) DEFAULT NULL,
  `reference_stock_exchange` char(1) DEFAULT NULL,
  `clearing_system_code` char(1) DEFAULT NULL,
  `min_amount_agreed` decimal(15,4) DEFAULT NULL,
  `max_amount_routed_orders` decimal(15,4) DEFAULT NULL,
  `stipulation_type` char(5) DEFAULT NULL,
  `thr_sta_block_perc` decimal(5,2) DEFAULT NULL,
  `min_amount_parametrised` decimal(15,4) DEFAULT NULL,
  `coupon_period_month` int(11) DEFAULT NULL,
  `maturity_perc` decimal(8,4) DEFAULT NULL,
  `benchmark` char(1) DEFAULT NULL,
  `segregable` char(1) DEFAULT NULL,
  `issue_amount_alive` decimal(20,5) DEFAULT NULL,
  `coupon_calc_mode` char(1) DEFAULT NULL,
  `amortization_type` char(2) DEFAULT NULL,
  `interest_accrual_date` date DEFAULT NULL,
  `security_type` int(11) DEFAULT NULL,
  `min_trade_vol` decimal(22,8) DEFAULT NULL,
  `round_lot` decimal(22,8) DEFAULT NULL,
  `facial` decimal(13,6) DEFAULT NULL,
  `calc_mode` int(11) DEFAULT NULL,
  `fecha_valor` date DEFAULT NULL,
  `issuer_code_new` varchar(50) DEFAULT NULL,
  `coupon_prv_date` date DEFAULT NULL,
  `outstanding_capital` decimal(20,5) DEFAULT NULL,
  `number_holders` int(11) DEFAULT NULL,
  `outstanding_shares` bigint(20) DEFAULT NULL COMMENT 'numero de acciones',
  `minimum_capital` decimal(15,5) DEFAULT NULL,
  `minimum_auth_shares` int(11) DEFAULT NULL,
  `short_name` varchar(80) DEFAULT NULL,
  `fund_master_name` varchar(50) DEFAULT NULL,
  `fund_mng` varchar(50) DEFAULT NULL,
  `fund_depos` varchar(50) DEFAULT NULL,
  `fund_type` varchar(32) DEFAULT NULL,
  `fund_min_subs` decimal(16,8) DEFAULT NULL,
  `fund_min_rem` decimal(16,8) DEFAULT NULL,
  `fund_time_end` time DEFAULT NULL,
  `fund_clear_days` int(11) DEFAULT NULL,
  `ref_prc` decimal(22,8) DEFAULT NULL,
  `max_trade_vol` decimal(22,8) DEFAULT NULL,
  `repo_start_date` date DEFAULT NULL,
  `repo_end_date` date DEFAULT NULL,
  `repo_agreement_id` varchar(32) DEFAULT NULL,
  `repo_prc` decimal(19,5) DEFAULT NULL,
  `benchmark_id` varchar(32) DEFAULT NULL,
  `coupon_day_count` int(11) DEFAULT NULL,
  `yield_type` varchar(32) DEFAULT NULL,
  `yield` decimal(19,5) DEFAULT NULL,
  `yield_redem_date` date DEFAULT NULL,
  `yield_redem_prc` decimal(19,5) DEFAULT NULL,
  `price_type` int(11) DEFAULT NULL,
  `entitlement_id` int(11) DEFAULT NULL COMMENT 'Entitlement ID',
  `adnt` int(11) DEFAULT NULL COMMENT 'Average Daily Number Transaction',
  PRIMARY KEY (`exchange`,`vt_id`),
  UNIQUE KEY `exc_tpc` (`exchange`,`ticker_plant_code`),
  UNIQUE KEY `exc_isin` (`exchange`,`isin`,`real_mic`,`currency`),
  UNIQUE KEY `exc_tckr` (`exchange`,`ticker`,`real_mic`,`currency`),
  UNIQUE KEY `exc_wkn` (`exchange`,`wkn_no`),
  KEY `exc_chang` (`exchange`,`changed_time`) USING BTREE,
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_event` (`exchange`,`event_time`) USING BTREE,
  KEY `idx_isin` (`isin`),
  KEY `idx_mic_sym_ccy` (`mic`,`ticker`,`currency`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `security_deleted`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `security_deleted` (
  `exchange` char(8) NOT NULL,
  `vt_id` char(40) NOT NULL,
  `ticker` char(48) NOT NULL,
  `isin` char(12) DEFAULT NULL,
  `sedol` char(7) DEFAULT NULL,
  `cusip` char(9) DEFAULT NULL,
  `local_code` char(9) DEFAULT NULL,
  `ticker_plant_code` char(32) DEFAULT NULL,
  `event_type` char(1) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `created_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `changed_time` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `inst_status_type` char(1) DEFAULT NULL,
  `ticker_plant_flag` char(1) DEFAULT NULL,
  `subexchange` char(8) DEFAULT NULL,
  `inst_type` char(1) DEFAULT NULL,
  `inst_subtype` char(1) DEFAULT NULL,
  `name` char(150) DEFAULT NULL,
  `country` char(3) DEFAULT NULL,
  `issue_amount` decimal(22,8) DEFAULT NULL,
  `issue_price` decimal(22,8) DEFAULT NULL,
  `issue_date` date DEFAULT NULL,
  `issuer_code` char(8) DEFAULT NULL,
  `quotation_type` char(1) DEFAULT NULL,
  `currency` char(3) DEFAULT NULL,
  `currency_precision` char(1) DEFAULT NULL,
  `lot_size` int(11) DEFAULT NULL,
  `tick_size` decimal(12,8) DEFAULT NULL,
  `closing_date` date DEFAULT NULL,
  `closing_date_type` char(1) DEFAULT NULL,
  `thr_sta_perc` decimal(5,2) DEFAULT NULL,
  `thr_sta_low_prc` decimal(19,5) DEFAULT NULL,
  `thr_sta_high_prc` decimal(19,5) DEFAULT NULL,
  `thr_dyn_perc` decimal(5,2) DEFAULT NULL,
  `thr_dyn_low_prc` decimal(19,5) DEFAULT NULL,
  `thr_dyn_high_prc` decimal(19,5) DEFAULT NULL,
  `exercise_prc` decimal(15,8) DEFAULT NULL,
  `exercise_date` date DEFAULT NULL COMMENT 'fecha de ejercicio',
  `contract_multiplier` decimal(19,9) DEFAULT NULL,
  `udlying_id` char(32) DEFAULT NULL,
  `udlying_isin` char(12) DEFAULT NULL,
  `udlying_type` char(3) DEFAULT NULL,
  `dayprv_close_prc` decimal(19,5) DEFAULT NULL,
  `dayprv_close_yield` decimal(15,8) DEFAULT NULL,
  `dayprv_close_prc_type` char(1) DEFAULT NULL,
  `dayprv_close_prc_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `dayprv_tot_vol` decimal(12,0) DEFAULT NULL,
  `dayprv_tot_turn` decimal(22,3) DEFAULT NULL,
  `yearprv_close_prc` decimal(19,5) DEFAULT NULL,
  `year_low_prc` decimal(19,5) DEFAULT NULL,
  `year_low_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_high_prc` decimal(19,5) DEFAULT NULL,
  `year_high_date` timestamp NOT NULL DEFAULT '0000-00-00 00:00:00',
  `year_tot_vol` decimal(12,0) DEFAULT NULL,
  `year_tot_turn` decimal(22,3) DEFAULT NULL,
  `data_source` char(2) DEFAULT NULL,
  `cfi` char(6) DEFAULT NULL,
  `ric` char(15) DEFAULT NULL,
  `mic` char(4) DEFAULT NULL,
  `real_mic` char(4) DEFAULT 'NONE',
  `barrier_prc` decimal(13,5) DEFAULT NULL,
  `war_type` char(1) DEFAULT NULL,
  `wkn_no` char(9) DEFAULT NULL,
  `tick_table` int(11) DEFAULT NULL,
  `nav` decimal(18,8) DEFAULT NULL,
  `nav_date` date DEFAULT NULL,
  `owner_member` int(11) DEFAULT NULL,
  `clearer_member` int(11) DEFAULT NULL,
  `product_type` varchar(2) DEFAULT NULL,
  `coupon_period` char(1) DEFAULT NULL,
  `coupon_type` char(1) DEFAULT NULL,
  `coupon_next_date` date DEFAULT NULL,
  `payment_type` char(1) DEFAULT NULL,
  `quotation_modality` char(1) DEFAULT NULL,
  `perpetual_ind` char(1) DEFAULT NULL,
  `interest_rate` decimal(13,5) DEFAULT NULL,
  `next_amortization_date` date DEFAULT NULL,
  `accrued_interest` decimal(13,6) DEFAULT NULL,
  `low_barrier_prc` decimal(13,5) DEFAULT NULL,
  `high_barrier_prc` decimal(13,5) DEFAULT NULL,
  `first_trading_date` date DEFAULT NULL,
  `last_trading_date` date DEFAULT NULL,
  `fee_type` char(2) DEFAULT NULL,
  `trading_scope` char(1) DEFAULT NULL,
  `reference_stock_exchange` char(1) DEFAULT NULL,
  `clearing_system_code` char(1) DEFAULT NULL,
  `min_amount_agreed` decimal(15,4) DEFAULT NULL,
  `max_amount_routed_orders` decimal(15,4) DEFAULT NULL,
  `stipulation_type` char(5) DEFAULT NULL,
  `thr_sta_block_perc` decimal(5,2) DEFAULT NULL,
  `min_amount_parametrised` decimal(15,4) DEFAULT NULL,
  `coupon_period_month` int(11) DEFAULT NULL,
  `maturity_perc` decimal(8,4) DEFAULT NULL,
  `benchmark` char(1) DEFAULT NULL,
  `segregable` char(1) DEFAULT NULL,
  `issue_amount_alive` decimal(20,5) DEFAULT NULL,
  `coupon_calc_mode` char(1) DEFAULT NULL,
  `amortization_type` char(2) DEFAULT NULL,
  `interest_accrual_date` date DEFAULT NULL,
  `security_type` int(11) DEFAULT NULL,
  `min_trade_vol` decimal(22,8) DEFAULT NULL,
  `round_lot` decimal(22,8) DEFAULT NULL,
  `facial` decimal(13,6) DEFAULT NULL,
  `calc_mode` int(11) DEFAULT NULL,
  `fecha_valor` date DEFAULT NULL,
  `issuer_code_new` varchar(50) DEFAULT NULL,
  `coupon_prv_date` date DEFAULT NULL,
  `outstanding_capital` decimal(20,5) DEFAULT NULL,
  `number_holders` int(11) DEFAULT NULL,
  `outstanding_shares` bigint(20) DEFAULT NULL COMMENT 'numero de acciones',
  `minimum_capital` decimal(15,5) DEFAULT NULL,
  `minimum_auth_shares` int(11) DEFAULT NULL,
  `short_name` varchar(80) DEFAULT NULL,
  `fund_master_name` varchar(50) DEFAULT NULL,
  `fund_mng` varchar(50) DEFAULT NULL,
  `fund_depos` varchar(50) DEFAULT NULL,
  `fund_type` varchar(32) DEFAULT NULL,
  `fund_min_subs` decimal(16,8) DEFAULT NULL,
  `fund_min_rem` decimal(16,8) DEFAULT NULL,
  `fund_time_end` time DEFAULT NULL,
  `fund_clear_days` int(11) DEFAULT NULL,
  `ref_prc` decimal(22,8) DEFAULT NULL,
  `max_trade_vol` decimal(22,8) DEFAULT NULL,
  `repo_start_date` date DEFAULT NULL,
  `repo_end_date` date DEFAULT NULL,
  `repo_agreement_id` varchar(32) DEFAULT NULL,
  `repo_prc` decimal(19,5) DEFAULT NULL,
  `benchmark_id` varchar(32) DEFAULT NULL,
  `coupon_day_count` int(11) DEFAULT NULL,
  `yield_type` varchar(32) DEFAULT NULL,
  `yield` decimal(19,5) DEFAULT NULL,
  `yield_redem_date` date DEFAULT NULL,
  `yield_redem_prc` decimal(19,5) DEFAULT NULL,
  `price_type` int(11) DEFAULT NULL,
  `entitlement_id` int(11) DEFAULT NULL COMMENT 'Entitlement ID',
  `adnt` int(11) DEFAULT NULL COMMENT 'Average Daily Number Transaction',
  PRIMARY KEY (`exchange`,`vt_id`),
  UNIQUE KEY `exc_isin` (`exchange`,`isin`,`real_mic`,`currency`),
  UNIQUE KEY `exc_tckr` (`exchange`,`ticker`,`real_mic`,`currency`),
  UNIQUE KEY `exc_wkn` (`exchange`,`wkn_no`),
  KEY `exc_chang` (`exchange`,`changed_time`) USING BTREE,
  KEY `chang` (`changed_time`) USING BTREE,
  KEY `exc_event` (`exchange`,`event_time`) USING BTREE,
  KEY `exc_tpc` (`exchange`,`ticker_plant_code`),
  KEY `idx_mic_event` (`mic`,`event_time`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `security_ft`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `security_ft` (
  `vt_exchange` char(4) NOT NULL,
  `ft_country_quotation` char(2) NOT NULL DEFAULT '',
  `ft_exchange_quotation` char(1) NOT NULL DEFAULT '',
  `ft_exchange_section` char(3) NOT NULL DEFAULT '',
  `ft_exchange_quotation2` char(1) NOT NULL DEFAULT '',
  `ft_ticker` char(15) NOT NULL DEFAULT '',
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `ft_isin` char(12) NOT NULL DEFAULT '',
  `ft_record_type` char(8) DEFAULT NULL,
  `ft_security_type` char(2) DEFAULT NULL,
  `ft_cusip` char(9) DEFAULT NULL,
  `ft_local_code_A` char(12) DEFAULT NULL,
  `ft_local_code_B` char(6) DEFAULT NULL,
  `ft_name` char(27) DEFAULT NULL,
  `ft_industrial_class` char(4) DEFAULT NULL,
  `ft_currency` char(3) DEFAULT NULL,
  `ft_nom_currency` char(3) DEFAULT NULL,
  PRIMARY KEY (`ft_country_quotation`,`ft_exchange_quotation`,`ft_exchange_section`,`ft_exchange_quotation2`,`ft_isin`,`ft_ticker`),
  KEY `vt_exchange` (`vt_exchange`,`ft_ticker`),
  KEY `vt_exchange_2` (`vt_exchange`,`ft_isin`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `security_history`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `security_history` (
  `exchange` char(8) DEFAULT NULL,
  `vt_id_old` char(40) DEFAULT NULL,
  `vt_id_new` char(40) DEFAULT NULL,
  `ticker_old` char(40) DEFAULT NULL,
  `ticker_new` char(40) DEFAULT NULL,
  `isin_old` char(12) DEFAULT NULL,
  `isin_new` char(12) DEFAULT NULL,
  `ticker_plant_code_old` varchar(32) DEFAULT NULL,
  `ticker_plant_code_new` varchar(32) DEFAULT NULL,
  `service` varchar(100) DEFAULT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  `comments` text,
  KEY `exc_vt_id_new` (`exchange`,`vt_id_new`),
  KEY `exc_vt_id_old` (`exchange`,`vt_id_old`),
  KEY `exc_ticker_new` (`exchange`,`ticker_new`),
  KEY `exc_ticker_old` (`exchange`,`ticker_old`),
  KEY `exc_tpc_new` (`exchange`,`ticker_plant_code_new`),
  KEY `exc_tpc_old` (`exchange`,`ticker_plant_code_old`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `security_type`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `security_type` (
  `type_exchange` char(4) NOT NULL,
  `type_id` int(11) NOT NULL,
  `type_desc_spa` char(100) NOT NULL,
  `type_desc_eng` char(100) NOT NULL,
  `exch_sec_type` varchar(50) NOT NULL,
  PRIMARY KEY (`type_exchange`,`type_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `tick_range`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `tick_range` (
  `range_id` int(10) unsigned NOT NULL AUTO_INCREMENT,
  `low_prc` decimal(18,8) NOT NULL DEFAULT '-9999999999.99999999',
  `high_prc` decimal(18,8) NOT NULL DEFAULT '9999999999.99999999',
  `tick` decimal(20,10) NOT NULL DEFAULT '0.0000000000',
  `decimals` int(10) unsigned NOT NULL DEFAULT '0',
  `created_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`range_id`),
  UNIQUE KEY `rang` (`low_prc`,`high_prc`,`tick`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `tick_table`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `tick_table` (
  `table_id` int(10) unsigned NOT NULL AUTO_INCREMENT,
  `created_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`table_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `tick_table_range`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `tick_table_range` (
  `tick_table_table_id` int(10) unsigned NOT NULL,
  `tick_range_range_id` int(10) unsigned NOT NULL,
  `created_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP,
  PRIMARY KEY (`tick_table_table_id`,`tick_range_range_id`),
  KEY `tick_table_has_tick_range_FKIndex1` (`tick_table_table_id`),
  KEY `tick_table_has_tick_range_FKIndex2` (`tick_range_range_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `user_grp_ss`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `user_grp_ss` (
  `grp_id` bigint(20) NOT NULL,
  `user_id` char(16) NOT NULL,
  `firm_id` char(8) NOT NULL,
  `name` char(150) NOT NULL,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  `grp_type` int(11) NOT NULL,
  `sty_list` blob,
  PRIMARY KEY (`firm_id`,`user_id`,`grp_id`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `user_grp_sty_ss`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!40101 SET character_set_client = utf8 */;
CREATE TABLE `user_grp_sty_ss` (
  `exchange` char(8) NOT NULL,
  `symbol` char(48) NOT NULL,
  `currency` char(3) NOT NULL,
  `sty_id` int(11) NOT NULL AUTO_INCREMENT,
  `event_time` timestamp NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
  PRIMARY KEY (`sty_id`),
  UNIQUE KEY `exchange` (`exchange`,`symbol`,`currency`)
) ENGINE=MyISAM DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping routines for database 'nodes'
--
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed

--
-- Dbmate schema migrations
--

LOCK TABLES `schema_migrations` WRITE;
INSERT INTO `schema_migrations` (version) VALUES
  ('20190830103614'),
  ('20190830103615'),
  ('20190830103616'),
  ('20190830103617'),
  ('20190830103618'),
  ('20190830103620'),
  ('20190830103621'),
  ('20190830103622'),
  ('20190830103623'),
  ('20190830103624'),
  ('20190830103625'),
  ('20190830103626'),
  ('20190830103627'),
  ('20190830103628'),
  ('20190830103629'),
  ('20190830103630'),
  ('20190830103631'),
  ('20190830103632'),
  ('20190830103633'),
  ('20190830103634'),
  ('20190830103635'),
  ('20190830103636'),
  ('20190830103637'),
  ('20190830103638'),
  ('20190830103639'),
  ('20190830103640'),
  ('20190830103641'),
  ('20190830103642'),
  ('20190830103643'),
  ('20190830103644'),
  ('20190830103645'),
  ('20190830103646'),
  ('20190830103647'),
  ('20190830103648'),
  ('20190830103649'),
  ('20190909082221'),
  ('20190909082230'),
  ('20191003123143'),
  ('20191003131213'),
  ('20191007134011'),
  ('20191010134628'),
  ('20200305084728'),
  ('20200318103429'),
  ('20200416071233'),
  ('20200417075351'),
  ('20200707110310'),
  ('20200709172016'),
  ('20200713072219'),
  ('20200803074103'),
  ('20200825082607'),
  ('20200826132104'),
  ('20200922131438'),
  ('20201021122000'),
  ('20201027124810'),
  ('20201105123000'),
  ('20201110151500'),
  ('20210518114217'),
  ('20210518150045'),
  ('20210518153811'),
  ('20210727092004'),
  ('20211209105837'),
  ('20220520081335'),
  ('20220522161939');
UNLOCK TABLES;
